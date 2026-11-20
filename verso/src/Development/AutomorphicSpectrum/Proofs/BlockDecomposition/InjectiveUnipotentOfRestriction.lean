import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FiniteDimInvariantSubspaceAdjointPair
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ExistsOrderedCreationList
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviCommuteUnipotentBoundaryStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviAdjointOnChainsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteLeviStableChainsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviRaisingKillsTopChainStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundaryProdCreationLeviChainsStatement

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

/- English proof (translation)
Establish `h1 : ∀ l : Lt n, ¬inUU lev l → annL l x = 0` using `fun l hl => by`. Use function extensionality and compare the values at `A`. Assume the negation of the conclusion as `h`. Conclude with `hl (hx _ (annL_ne h).2 l (mem_insert_self _ _))`. Establish `h2 : ∀ l m : Lt n, ¬inUU lev m → annL m (annL l x) = 0` using `fun l m hm => by`.

Use function extensionality and compare the values at `A`. Assume the negation of the conclusion as `h`. Take `⟨-, h3⟩` from `annL_ne h`. Take `⟨-, h4⟩` from `annL_ne h3`. Conclude with `hm (hx _ h4 m (mem_insert_of_mem (mem_insert_self _ _)))`.

Simplify using `only [bdL, LinearMap.add_apply, LinearMap.sum_apply]`. Use `congr 1`. Use `sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : inUU lev l`. Rewrite using `[if_pos (Or.inr hl : inRR lev l), if_pos hl]`.

Rewrite using `[if_neg hl] split_ifs`. Simplify using `[Module.End.mul_apply, h1 l hl]`. Both sides reduce to the same expression. Use `sum_congr rfl fun l _ => sum_congr rfl fun m _ => sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hl : inUU lev l`.

Distinguish the cases in `hm : inUU lev m`. Distinguish the cases in `hc : l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2`. Rewrite using `[if_pos ⟨Or.inr hl, Or.inr hm, hc⟩, if_pos ⟨hl, hm, hc⟩]`. Rewrite using `[if_neg fun t => hc t.2.2, if_neg fun t => hc t.2.2]`. Establish `hn : ¬(inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2)` using `fun t => hm t.2.1`.

Rewrite using `[if_neg hn]`. Use `split_ifs`. Simplify using `[Module.End.mul_apply, h2 l m hm]`. Both sides reduce to the same expression. Establish `hn : ¬(inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2)` using `fun t => hl t.1`.

Rewrite using `[if_neg hn]`. Use `split_ifs`. Simplify using `[Module.End.mul_apply, h1 l hl]`. Both sides reduce to the same expression.
-/
theorem bdL_inRR_eq {n : ℕ} {lev : Fin n → ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) {x : Cq n V} (hx : SuppL (inUU lev) x) :
    bdL (inRR lev) E1 E2 x = bdL (inUU lev) E1 E2 x := by
  classical
  have h1 : ∀ l : Lt n, ¬inUU lev l → annL l x = 0 := fun l hl => by
    funext A
    by_contra h
    exact hl (hx _ (annL_ne h).2 l (mem_insert_self _ _))
  have h2 : ∀ l m : Lt n, ¬inUU lev m → annL m (annL l x) = 0 := fun l m hm => by
    funext A
    by_contra h
    obtain ⟨-, h3⟩ := annL_ne h
    obtain ⟨-, h4⟩ := annL_ne h3
    exact hm (hx _ h4 m (mem_insert_of_mem (mem_insert_self _ _)))
  simp only [bdL, LinearMap.add_apply, LinearMap.sum_apply]
  congr 1
  · refine sum_congr rfl fun l _ => ?_
    by_cases hl : inUU lev l
    · rw [if_pos (Or.inr hl : inRR lev l), if_pos hl]
    · rw [if_neg hl]
      split_ifs
      · simp [Module.End.mul_apply, h1 l hl]
      · rfl
  · refine sum_congr rfl fun l _ => sum_congr rfl fun m _ => sum_congr rfl fun k _ => ?_
    by_cases hl : inUU lev l
    · by_cases hm : inUU lev m
      · by_cases hc : l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧ k.2.1.2 = m.2.1.2
        · rw [if_pos ⟨Or.inr hl, Or.inr hm, hc⟩, if_pos ⟨hl, hm, hc⟩]
        · rw [if_neg fun t => hc t.2.2, if_neg fun t => hc t.2.2]
      · have hn : ¬(inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧
            k.2.1.2 = m.2.1.2) := fun t => hm t.2.1
        rw [if_neg hn]
        split_ifs
        · simp [Module.End.mul_apply, h2 l m hm]
        · rfl
    · have hn : ¬(inUU lev l ∧ inUU lev m ∧ l.2.1.2 = m.2.1.1 ∧ k.1 = xor l.1 m.1 ∧ k.2.1.1 = l.2.1.1 ∧
          k.2.1.2 = m.2.1.2) := fun t => hl t.1
      rw [if_neg hn]
      split_ifs
      · simp [Module.End.mul_apply, h1 l hl]
      · rfl

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Use function extensionality and compare the values at `A`. Rewrite using `[creL_apply, Pi.smul_apply]`. Distinguish the cases in `hA : A = insert f S`. Substitute `hA` using the available equality. Rewrite using `[if_pos (mem_insert_self f S), erase_insert h, Pi.single_eq_same, Pi.single_eq_same]`.

Rewrite using `[Pi.single_eq_of_ne hA, smul_zero] split_ifs with hf`. Establish `hne : A.erase f ≠ S` using `fun e => hA (by rw [← e, insert_erase hf])`. Rewrite using `[Pi.single_eq_of_ne hne, smul_zero]`. Both sides reduce to the same expression.
-/
theorem creL_single (f : Lt n) (S : Finset (Lt n)) (w : V) (h : f ∉ S) :
    (creL f : Module.End ℂ (Cq n V)) (Pi.single S w : Cq n V) =
      sgL f (insert f S) • (Pi.single (insert f S) w : Cq n V) := by
  funext A
  rw [creL_apply, Pi.smul_apply]
  by_cases hA : A = insert f S
  · subst hA
    rw [if_pos (mem_insert_self f S), erase_insert h, Pi.single_eq_same, Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hA, smul_zero]
    split_ifs with hf
    · have hne : A.erase f ≠ S := fun e => hA (by rw [← e, insert_erase hf])
      rw [Pi.single_eq_of_ne hne, smul_zero]
    · rfl

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => exact ⟨1, one_ne_zero, by simp⟩`. Consider the case `cons f t ih`. Rewrite `hl` using `[List.nodup_cons]`. Take `⟨c, hc, e⟩` from `ih hl.2 fun i hi => hS i (List.mem_cons_of_mem f hi)`.

Establish `hf : f ∉ S ∪ t.toFinset`. Rewrite using `[mem_union, not_or]`. Conclude with `⟨hS f List.mem_cons_self, fun h => hl.1 (List.mem_toFinset.1 h)⟩`. Establish `hU : S ∪ (f :: t).toFinset = insert f (S ∪ t.toFinset)`. Rewrite using `[List.toFinset_cons, union_insert]`.

Use `⟨c * sgL f (insert f (S ∪ t.toFinset)), mul_ne_zero hc (sgL_ne_zero _ _), ?_⟩` and prove the remaining obligations. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, e, map_smul, creL_single f _ w hf, hU, smul_smul]`.
-/
theorem prod_creL_single (l : List (Lt n)) (S : Finset (Lt n)) (w : V) (hl : l.Nodup) (hS : ∀ i ∈ l, i ∉ S) :
    ∃ c : ℂ, c ≠ 0 ∧
      ((l.map creL).prod : Module.End ℂ (Cq n V)) (Pi.single S w : Cq n V) = c • (Pi.single (S ∪ l.toFinset) w : Cq n V) := by
  induction l with
  | nil => exact ⟨1, one_ne_zero, by simp⟩
  | cons f t ih =>
    rw [List.nodup_cons] at hl
    obtain ⟨c, hc, e⟩ := ih hl.2 fun i hi => hS i (List.mem_cons_of_mem f hi)
    have hf : f ∉ S ∪ t.toFinset := by
      rw [mem_union, not_or]
      exact ⟨hS f List.mem_cons_self, fun h => hl.1 (List.mem_toFinset.1 h)⟩
    have hU : S ∪ (f :: t).toFinset = insert f (S ∪ t.toFinset) := by
      rw [List.toFinset_cons, union_insert]
    refine ⟨c * sgL f (insert f (S ∪ t.toFinset)), mul_ne_zero hc (sgL_ne_zero _ _), ?_⟩
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, e, map_smul, creL_single f _ w hf, hU, smul_smul]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simpa using And.intro hx hd`. Consider the case `cons i l ih`. Take `⟨ih1, ih2⟩` from `ih fun k hk => hl k (List.mem_cons_of_mem i hk)`. Establish `hi : P i` using `hl i List.mem_cons_self`.

Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]`. Prove the components needed by the constructor for the conclusion. Introduce `A hA k hk`. Take `⟨h1, h2⟩` from `creL_ne hA`. Distinguish the cases in `hki : k = i`.

Conclude with `hki ▸ hi`. Conclude with `ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)`. Introduce `A hA`. Take `⟨h1, h2⟩` from `creL_ne hA`. Establish `h3` using `ih2 _ h2`.

Establish `h4` using `Finset.card_erase_add_one h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem suppL_degL_prod (P : Lt n → Prop) (l : List (Lt n)) (x : Cq n V) (j : ℕ) (hl : ∀ i ∈ l, P i)
    (hx : SuppL P x) (hd : DegL j x) :
    SuppL P (((l.map creL).prod : Module.End ℂ (Cq n V)) x) ∧
      DegL (j + l.length) (((l.map creL).prod : Module.End ℂ (Cq n V)) x) := by
  induction l with
  | nil => simpa using And.intro hx hd
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih fun k hk => hl k (List.mem_cons_of_mem i hk)
    have hi : P i := hl i List.mem_cons_self
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.length_cons]
    constructor
    · intro A hA k hk
      obtain ⟨h1, h2⟩ := creL_ne hA
      by_cases hki : k = i
      · exact hki ▸ hi
      · exact ih1 _ h2 k (Finset.mem_erase.2 ⟨hki, hk⟩)
    · intro A hA
      obtain ⟨h1, h2⟩ := creL_ne hA
      have h3 := ih2 _ h2
      have h4 := Finset.card_erase_add_one h1
      omega

end GlobalTheory.CompanionTheory.LvChain

namespace GlobalTheory.CompanionTheory.LvChain

open GlobalTheory.CompanionTheory.FarReg in

/- English proof (translation)
Set `e : Cq n V ≃ₗ[ℂ] PiLp 2 (fun _ : Finset (Lt n) => V)` to `(WithLp.linearEquiv 2 ℂ (Finset (Lt n) → V)).symm`. Set `c : Module.End ℂ (Cq n V) → Module.End ℂ (PiLp 2 (fun _ : Finset (Lt n) => V))` to `fun f => (e : Cq n V →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] Cq n V)`. Establish `hc : ∀ f x, c f (e x) = e (f x)` using `fun f x => by simp [c]`. Use `haveI : FiniteDimensional ℂ (T.map e.toLinearMap) := Module.Finite.map T _`. Establish `key` using `highest_preimage_inner (T.map e.toLinearMap) (fun i => c (a i)) (fun i => c (b i)) (c D) (e y) inferInstance ?_ ?_ ?_ ?_ ?_ ⟨y, hy, rfl⟩ ?_`.

Take `⟨_, ⟨y', hy', rfl⟩, h1, h2⟩` from `key`. Use `⟨y', hy', fun i => e.injective ?_, e.injective ?_⟩` and prove the remaining obligations. Use `h1 i` as an intermediate fact. Simplify `this` using `[hc]`. Use `h2` as an intermediate fact.

Simplify `this` using `[hc]`. Introduce `i x z`. Take `⟨x, rfl⟩` from `e.surjective x`. Take `⟨z, rfl⟩` from `e.surjective z`. Use `show ⟪c (a i) (e x), e z⟫_ℂ = ⟪e x, c (b i) (e z)⟫_ℂ`.

Rewrite using `[hc, hc, PiLp.inner_apply, PiLp.inner_apply]`. Conclude with `hadj i x z`. Introduce and unpack `i _ ⟨t, ht, rfl⟩`. Conclude with `⟨a i t, haT i t ht, (hc _ _).symm⟩`. Introduce and unpack `i _ ⟨t, ht, rfl⟩`.

Conclude with `⟨b i t, hbT i t ht, (hc _ _).symm⟩`. Introduce and unpack `i _ ⟨t, ht, rfl⟩ show c (a i) (c D (e t)) = c D (c (a i) (e t))`. Simplify using `only [hc, haD i t ht]`. Introduce and unpack `i _ ⟨t, ht, rfl⟩ show c (b i) (c D (e t)) = c D (c (b i) (e t))`. Simplify using `only [hc, hbD i t ht]`.

Introduce `i show c (a i) (c D (e y)) = 0`. Simplify using `only [hc, hDy i, map_zero]`.
-/
theorem highest_preimage {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}
    (T : Submodule ℂ (Cq n V)) (a b : ι → Module.End ℂ (Cq n V)) (D : Module.End ℂ (Cq n V)) (y : Cq n V)
    (hT : FiniteDimensional ℂ T) (hadj : ∀ i x z, ∑ A, ⟪a i x A, z A⟫_ℂ = ∑ A, ⟪x A, b i z A⟫_ℂ)
    (haT : ∀ i, ∀ t ∈ T, a i t ∈ T) (hbT : ∀ i, ∀ t ∈ T, b i t ∈ T)
    (haD : ∀ i, ∀ t ∈ T, a i (D t) = D (a i t)) (hbD : ∀ i, ∀ t ∈ T, b i (D t) = D (b i t))
    (hy : y ∈ T) (hDy : ∀ i, a i (D y) = 0) : ∃ y' ∈ T, (∀ i, a i y' = 0) ∧ D y' = D y := by
  let e : Cq n V ≃ₗ[ℂ] PiLp 2 (fun _ : Finset (Lt n) => V) := (WithLp.linearEquiv 2 ℂ (Finset (Lt n) → V)).symm
  let c : Module.End ℂ (Cq n V) → Module.End ℂ (PiLp 2 (fun _ : Finset (Lt n) => V)) := fun f =>
    (e : Cq n V →ₗ[ℂ] _) ∘ₗ f ∘ₗ (e.symm : _ →ₗ[ℂ] Cq n V)
  have hc : ∀ f x, c f (e x) = e (f x) := fun f x => by simp [c]
  haveI : FiniteDimensional ℂ (T.map e.toLinearMap) := Module.Finite.map T _
  have key := highest_preimage_inner (T.map e.toLinearMap) (fun i => c (a i)) (fun i => c (b i)) (c D) (e y)
    inferInstance ?_ ?_ ?_ ?_ ?_ ⟨y, hy, rfl⟩ ?_
  · obtain ⟨_, ⟨y', hy', rfl⟩, h1, h2⟩ := key
    refine ⟨y', hy', fun i => e.injective ?_, e.injective ?_⟩
    · have := h1 i
      simpa [hc] using this
    · have := h2
      simpa [hc] using this
  · intro i x z
    obtain ⟨x, rfl⟩ := e.surjective x
    obtain ⟨z, rfl⟩ := e.surjective z
    show ⟪c (a i) (e x), e z⟫_ℂ = ⟪e x, c (b i) (e z)⟫_ℂ
    rw [hc, hc, PiLp.inner_apply, PiLp.inner_apply]
    exact hadj i x z
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨a i t, haT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    exact ⟨b i t, hbT i t ht, (hc _ _).symm⟩
  · rintro i _ ⟨t, ht, rfl⟩
    show c (a i) (c D (e t)) = c D (c (a i) (e t))
    simp only [hc, haD i t ht]
  · rintro i _ ⟨t, ht, rfl⟩
    show c (b i) (c D (e t)) = c D (c (b i) (e t))
    simp only [hc, hbD i t ht]
  · intro i
    show c (a i) (c D (e y)) = 0
    simp only [hc, hDy i, map_zero]

/- English proof (translation)
Introduce `hR n lam hlam lev hlev V _ _ E1 E2 hA u y hu hy hd hb`. Establish `hm : Monotone lev` using `hlev.1`. Establish `hP : IsPairA E1 E2` using `⟨hA.gl1, hA.gl2, hA.comm⟩`. Establish `hup : ∀ a b : Fin n, a < b → kA E1 E2 a b u = 0` using `fun a b hab => hu.2 a b hab rfl`. Take `⟨T, hTf, hyT, hTS, hTs⟩` from `GlobalTheory.T.exists_finite_levi_stable_chains n lev V E1 E2 _ y hA.locFin hy hd`.

Establish `hC` using `GlobalTheory.T.levi_commute_unipotent_boundary n lev V E1 E2 hm hP`. Establish `hone` using `GlobalTheory.T.levi_raising_kills_top_chain n lev V E1 E2 u hup`. Take `⟨y', hy'T, hy'0, hy'b⟩` from `highest_preimage (ι := {pq : Fin n × Fin n // pq.1 < pq.2 ∧ lev pq.1 = lev pq.2}) T (fun i => Lv lev E1 E2 i.1.1 i.1.2) (fun i => Lv lev E1 E2 i.1.2 i.1.1) (bdL (inUU lev) E1 E2) y hTf (fun i x z => GlobalTheory.T.levi_adjoint_on_chains n lev V E1 E2 hA.unitK _ _ i.2.2 x z) (fun …`. Take `⟨hy's, hy'd⟩` from `hTS y' hy'T`. Take `⟨l, hnd, hmem, hcl⟩` from `GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order n (fun _ => true) lev hm`.

Establish `hlc : ∀ e ∈ l, lev e.1.1 = lev e.1.2` using `fun e he => by`. Take `⟨-, h2⟩` from `(hmem e).1 he`. Use `le_antisymm (hm e.2.le) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h3`. Conclude with `h2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, not_le.1 h3⟩)`.

Establish `hbd` using `GlobalTheory.T.boundary_prod_creation_levi_chains n lev V E1 E2 l y' hlc hcl hy's (fun e he => hy'0 ⟨e.1, e.2, hlc e he⟩)`. Rewrite `hbd` using `[bdL_inRR_eq E1 E2 hy's, hy'b, hb]`. Use `set l' : List (Lt n) := l.map fun i => (false, i) with hl'`. Establish `hmap : (l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))) = l'.map creL`. Rewrite using `[hl', List.map_map]`.

Both sides reduce to the same expression. Establish `hnd' : l'.Nodup` using `hnd.map fun a b h => (Prod.ext_iff.1 h).2`. Establish `hout : ∀ i ∈ l', i ∉ omU lev`. Introduce `i hi h`. Take `⟨e, he, rfl⟩` from `List.mem_map.1 hi`.

Use `(Finset.mem_filter.1 h).2.2` as an intermediate fact. Establish `h2` using `hlc e he`. Simplify using `only at this`. Use linear arithmetic over natural numbers and integers. Take `⟨c, hc0, hcw⟩` from `prod_creL_single (V := V) l' (omU lev) u hnd' hout`.

Establish `hun : omU lev ∪ l'.toFinset = omN n`. Use extensionality with `⟨t, i⟩`. Simplify using `only [Finset.mem_union, List.mem_toFinset, hl', List.mem_map, omU, omN, Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(h | ⟨e, -, h⟩)`.

Conclude with `h.1`. Conclude with `(Prod.ext_iff.1 h).1.symm`. Introduce and unpack `rfl`. Distinguish the cases in `h2 : lev i.1.1 < lev i.1.2`. Conclude with `Or.inl ⟨rfl, h2⟩`.

Use `Or.inr ⟨i, (hmem i).2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, fun h => h2 (Finset.mem_filter.1 h).2.2⟩, rfl⟩` and prove the remaining obligations. Establish `hcard : (omN n).card = (omU lev).card + l'.length`. Rewrite using `[← hun, Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hnd']`. Conclude with `Finset.disjoint_left.2 fun i h1 h2 => hout i (List.mem_toFinset.1 h2) h1`. Take `⟨hs1, hs2⟩` from `suppL_degL_prod (V := V) (inRR lev) l' y' _ (fun i hi => by obtain ⟨e, -, rfl⟩ := List.mem_map.1 hi; exact Or.inl rfl) (fun A hA i hi => Or.inr (hy's A hA i hi)) hy'd`.

Use `set C : Cq n V := ((l'.map creL).prod : Module.End ℂ (Cq n V)) y' with hCd`. Establish `hsm : ∀ (s : ℂ) (x : Cq n V) (A : Finset (Lt n)), (s • x) A ≠ 0 → x A ≠ 0` using `fun s x A h h0 => h (by simp [h0])`. Use `hR n lam hlam lev hlev V E1 E2 hA u ((c⁻¹ * (-1 : ℂ) ^ l.length) • C) hu ?_ ?_ ?_` and prove the remaining obligations. Conclude with `fun A hA' => hs1 A (hsm _ C A hA')`. Introduce `A hA'`.

Establish `h3` using `hs2 A (hsm _ C A hA')`. Rewrite using `[h3, hcard]`. Establish `: l'.length = l.length` using `by rw [hl', List.length_map]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[map_smul, hCd]`.

Rewrite `hbd` using `[hmap]`. Rewrite using `[hbd, hcw, hun, smul_smul, smul_smul]`. Establish `hlen : l'.length = l.length` using `by rw [hl', List.length_map]`. Establish `h1 : ((-1 : ℂ) ^ l.length) * ((-1 : ℂ) ^ l.length) = 1`. Rewrite using `[← mul_pow]`.

Simplify using the standard rewrite rules. Establish `h2 : c⁻¹ * (-1 : ℂ) ^ l.length * (-1 : ℂ) ^ l.length * c = 1`. Rewrite using `[mul_assoc c⁻¹, h1, mul_one, inv_mul_cancel₀ hc0]`. Rewrite using `[h2, one_smul]`.
-/
theorem injUU_of_injRL : InjRL → InjUU := by
  intro hR n lam hlam lev hlev V _ _ E1 E2 hA u y hu hy hd hb
  have hm : Monotone lev := hlev.1
  have hP : IsPairA E1 E2 := ⟨hA.gl1, hA.gl2, hA.comm⟩
  have hup : ∀ a b : Fin n, a < b → kA E1 E2 a b u = 0 := fun a b hab => hu.2 a b hab rfl
  obtain ⟨T, hTf, hyT, hTS, hTs⟩ := GlobalTheory.T.exists_finite_levi_stable_chains n lev V E1 E2 _ y hA.locFin hy hd
  have hC := GlobalTheory.T.levi_commute_unipotent_boundary n lev V E1 E2 hm hP
  have hone := GlobalTheory.T.levi_raising_kills_top_chain n lev V E1 E2 u hup
  obtain ⟨y', hy'T, hy'0, hy'b⟩ := highest_preimage
    (ι := {pq : Fin n × Fin n // pq.1 < pq.2 ∧ lev pq.1 = lev pq.2}) T
    (fun i => Lv lev E1 E2 i.1.1 i.1.2) (fun i => Lv lev E1 E2 i.1.2 i.1.1) (bdL (inUU lev) E1 E2) y hTf
    (fun i x z => GlobalTheory.T.levi_adjoint_on_chains n lev V E1 E2 hA.unitK _ _ i.2.2 x z)
    (fun i t ht => hTs _ _ i.2.2 t ht)
    (fun i t ht => hTs _ _ i.2.2.symm t ht)
    (fun i t _ => (LinearMap.congr_fun (hC _ _ i.2.2) t).symm ▸ rfl)
    (fun i t _ => (LinearMap.congr_fun (hC _ _ i.2.2.symm) t).symm ▸ rfl) hyT
    (fun i => by rw [hb]; exact hone _ _ i.2.1 i.2.2)
  obtain ⟨hy's, hy'd⟩ := hTS y' hy'T
  obtain ⟨l, hnd, hmem, hcl⟩ := GlobalTheory.CompanionTheory.RgClusterOrder.exists_inside_order n (fun _ => true) lev hm
  have hlc : ∀ e ∈ l, lev e.1.1 = lev e.1.2 := fun e he => by
    obtain ⟨-, h2⟩ := (hmem e).1 he
    refine le_antisymm (hm e.2.le) ?_
    by_contra h3
    exact h2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, not_le.1 h3⟩)
  have hbd := GlobalTheory.T.boundary_prod_creation_levi_chains n lev V E1 E2 l y' hlc hcl hy's
    (fun e he => hy'0 ⟨e.1, e.2, hlc e he⟩)
  rw [bdL_inRR_eq E1 E2 hy's, hy'b, hb] at hbd
  set l' : List (Lt n) := l.map fun i => (false, i) with hl'
  have hmap : (l.map fun i => (creL (false, i) : Module.End ℂ (Cq n V))) = l'.map creL := by
    rw [hl', List.map_map]; rfl
  have hnd' : l'.Nodup := hnd.map fun a b h => (Prod.ext_iff.1 h).2
  have hout : ∀ i ∈ l', i ∉ omU lev := by
    intro i hi h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
    have := (Finset.mem_filter.1 h).2.2
    have h2 := hlc e he
    simp only at this
    omega
  obtain ⟨c, hc0, hcw⟩ := prod_creL_single (V := V) l' (omU lev) u hnd' hout
  have hun : omU lev ∪ l'.toFinset = omN n := by
    ext ⟨t, i⟩
    simp only [Finset.mem_union, List.mem_toFinset, hl', List.mem_map, omU, omN, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · rintro (h | ⟨e, -, h⟩)
      · exact h.1
      · exact (Prod.ext_iff.1 h).1.symm
    · rintro rfl
      by_cases h2 : lev i.1.1 < lev i.1.2
      · exact Or.inl ⟨rfl, h2⟩
      · refine Or.inr ⟨i, (hmem i).2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩, fun h => h2 (Finset.mem_filter.1 h).2.2⟩, rfl⟩
  have hcard : (omN n).card = (omU lev).card + l'.length := by
    rw [← hun, Finset.card_union_of_disjoint, List.toFinset_card_of_nodup hnd']
    exact Finset.disjoint_left.2 fun i h1 h2 => hout i (List.mem_toFinset.1 h2) h1
  obtain ⟨hs1, hs2⟩ := suppL_degL_prod (V := V) (inRR lev) l' y' _
    (fun i hi => by obtain ⟨e, -, rfl⟩ := List.mem_map.1 hi; exact Or.inl rfl)
    (fun A hA i hi => Or.inr (hy's A hA i hi)) hy'd
  set C : Cq n V := ((l'.map creL).prod : Module.End ℂ (Cq n V)) y' with hCd
  have hsm : ∀ (s : ℂ) (x : Cq n V) (A : Finset (Lt n)), (s • x) A ≠ 0 → x A ≠ 0 :=
    fun s x A h h0 => h (by simp [h0])
  refine hR n lam hlam lev hlev V E1 E2 hA u ((c⁻¹ * (-1 : ℂ) ^ l.length) • C) hu ?_ ?_ ?_
  · exact fun A hA' => hs1 A (hsm _ C A hA')
  · intro A hA'
    have h3 := hs2 A (hsm _ C A hA')
    rw [h3, hcard]
    have : l'.length = l.length := by rw [hl', List.length_map]
    omega
  · rw [map_smul, hCd]
    rw [hmap] at hbd
    rw [hbd, hcw, hun, smul_smul, smul_smul]
    have hlen : l'.length = l.length := by rw [hl', List.length_map]
    have h1 : ((-1 : ℂ) ^ l.length) * ((-1 : ℂ) ^ l.length) = 1 := by
      rw [← mul_pow]; simp
    have h2 : c⁻¹ * (-1 : ℂ) ^ l.length * (-1 : ℂ) ^ l.length * c = 1 := by
      rw [mul_assoc c⁻¹, h1, mul_one, inv_mul_cancel₀ hc0]
    rw [h2, one_smul]

end GlobalTheory.CompanionTheory.LvChain

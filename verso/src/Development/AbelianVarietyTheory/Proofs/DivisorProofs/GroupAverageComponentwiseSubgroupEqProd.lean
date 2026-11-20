import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubgroupAverageLinearTranslateConst

open Filter GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.AvgRestr

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
private lemma mem_rStab_iff_forall_mul_right_invariant {H : Type} [Group H] (u : H → ℂ) (k : H) :
    k ∈ rStab u ↔ ∀ x, u (x * k) = u x := Iff.rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma avg_eq_inv_index_mul_finsum_rStab_quotient {H : Type} [Group H] (u : H → ℂ) :
    avg u = ((rStab u).index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ rStab u, u q.out := rfl

/- English proof (translation)
Establish `h : ((x : H ⧸ rStab u).out)⁻¹ * x ∈ rStab u` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : H ⧸ rStab u))`. Establish `h2` using `(mem_rStab_iff_forall_mul_right_invariant u _).mp h ((x : H ⧸ rStab u).out)`. Rewrite `h2` using `[mul_inv_cancel_left]`. Conclude with `h2.symm`.
-/
lemma apply_out {H : Type} [Group H] (u : H → ℂ) (x : H) : u ((x : H ⧸ rStab u).out) = u x := by
  have h : ((x : H ⧸ rStab u).out)⁻¹ * x ∈ rStab u :=
    QuotientGroup.eq.mp (QuotientGroup.out_eq' (x : H ⧸ rStab u))
  have h2 := (mem_rStab_iff_forall_mul_right_invariant u _).mp h ((x : H ⧸ rStab u).out)
  rw [mul_inv_cancel_left] at h2
  exact h2.symm

/- English proof (translation)
Use extensionality with `k`. Rewrite using `[Subgroup.mem_comap, mem_rStab_iff_forall_mul_right_invariant, mem_rStab_iff_forall_mul_right_invariant]`. Prove the components needed by the constructor for the conclusion. Introduce `h y`. Take `⟨x, rfl⟩` from `hπ y`.

Establish `h2` using `h x`. Simplify `h2` using `[Function.comp, map_mul]`. Introduce `h x`. Simplify using `only [Function.comp_apply, map_mul]`. Conclude with `h (π x)`.
-/
private lemma rStab_comp_eq_comap_of_surjective {A B : Type} [Group A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (v : B → ℂ) : rStab (v ∘ π) = (rStab v).comap π := by
  ext k
  rw [Subgroup.mem_comap, mem_rStab_iff_forall_mul_right_invariant, mem_rStab_iff_forall_mul_right_invariant]
  constructor
  · intro h y
    obtain ⟨x, rfl⟩ := hπ y
    have h2 := h x
    simpa [Function.comp, map_mul] using h2
  · intro h x
    simp only [Function.comp_apply, map_mul]
    exact h (π x)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `q q' h`. Establish `h2` using `QuotientGroup.eq.mp h`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_comap, map_mul, map_inv]`. Conclude with `h2`.

Introduce `z`. Take `⟨a, ha⟩` from `hπ z.out`. Use `⟨(a : A ⧸ S.comap π), ?_⟩` and prove the remaining obligations. Establish `h2` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : A ⧸ S.comap π))`. Rewrite `h2` using `[Subgroup.mem_comap, map_mul, map_inv]`.

Use `show ((π (a : A ⧸ S.comap π).out : B) : B ⧸ S) = z`. Rewrite using `[← QuotientGroup.out_eq' z, ← ha, QuotientGroup.eq]`. Conclude with `h2`.
-/
private lemma bijective_quotient_comap_of_surjective {A B : Type} [Group A] [Group B] (π : A →* B)
    (hπ : Function.Surjective π) (S : Subgroup B) :
    Function.Bijective (fun q : A ⧸ S.comap π => ((π q.out : B) : B ⧸ S)) := by
  constructor
  · intro q q' h
    have h2 := QuotientGroup.eq.mp h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_comap,
      map_mul, map_inv]
    exact h2
  · intro z
    obtain ⟨a, ha⟩ := hπ z.out
    refine ⟨(a : A ⧸ S.comap π), ?_⟩
    have h2 := QuotientGroup.eq.mp (QuotientGroup.out_eq' (a : A ⧸ S.comap π))
    rw [Subgroup.mem_comap, map_mul, map_inv] at h2
    show ((π (a : A ⧸ S.comap π).out : B) : B ⧸ S) = z
    rw [← QuotientGroup.out_eq' z, ← ha, QuotientGroup.eq]
    exact h2

/- English proof (translation)
Rewrite using `[avg_eq_inv_index_mul_finsum_rStab_quotient, avg_eq_inv_index_mul_finsum_rStab_quotient, rStab_comp_eq_comap_of_surjective π hπ v]`. Set `e` to `Equiv.ofBijective _ (bijective_quotient_comap_of_surjective π hπ (rStab v))`. Establish `hidx : ((rStab v).comap π).index = (rStab v).index`. Rewrite using `[Subgroup.index_eq_card, Subgroup.index_eq_card]`. Conclude with `Nat.card_congr e`.

Rewrite using `[hidx]`. Use `congr 1`. Use `(finsum_congr ?_).trans (finsum_comp_equiv e (f := fun z : B ⧸ rStab v => v z.out))` and prove the remaining obligations. Introduce `q`. Conclude with `(apply_out v (π q.out)).symm`.
-/
theorem avg_comp_surj {A B : Type} [Group A] [Group B] (π : A →* B) (hπ : Function.Surjective π) (v : B → ℂ) :
    avg (v ∘ π) = avg v := by
  rw [avg_eq_inv_index_mul_finsum_rStab_quotient, avg_eq_inv_index_mul_finsum_rStab_quotient, rStab_comp_eq_comap_of_surjective π hπ v]
  let e := Equiv.ofBijective _ (bijective_quotient_comap_of_surjective π hπ (rStab v))
  have hidx : ((rStab v).comap π).index = (rStab v).index := by
    rw [Subgroup.index_eq_card, Subgroup.index_eq_card]
    exact Nat.card_congr e
  rw [hidx]
  congr 1
  refine (finsum_congr ?_).trans (finsum_comp_equiv e (f := fun z : B ⧸ rStab v => v z.out))
  intro q
  exact (apply_out v (π q.out)).symm

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `q q' h`. Rewrite using `[← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_pi]`. Introduce `j _`. Establish `h2` using `QuotientGroup.eq.mp (congrFun h j)`.

Simplify `h2` using `only [Pi.mul_apply, Pi.inv_apply]`. Introduce `z`. Use `⟨(((fun j => (z j).out) : ∀ j, M j) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Establish `hm` using `QuotientGroup.eq.mp (QuotientGroup.out_eq' ((((fun j => (z j).out) : ∀ j, M j)) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R))`.

Establish `hj` using `(Subgroup.mem_pi _).mp hm j (Set.mem_univ j)`. Simplify using `only [Pi.mul_apply, Pi.inv_apply] at hj`. Use `show ((_ : M j) : M j ⧸ R j) = z j`. Rewrite using `[← QuotientGroup.out_eq' (z j), QuotientGroup.eq]`. Conclude with `hj`.
-/
private lemma bijective_pi_quotient_to_quotient_pi {J : Type} (M : J → Type) [∀ j, Group (M j)] (R : ∀ j, Subgroup (M j)) :
    Function.Bijective
      (fun q : (∀ j, M j) ⧸ Subgroup.pi Set.univ R => fun j => ((q.out j : M j) : M j ⧸ R j)) := by
  constructor
  · intro q q' h
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq, Subgroup.mem_pi]
    intro j _
    have h2 := QuotientGroup.eq.mp (congrFun h j)
    simpa only [Pi.mul_apply, Pi.inv_apply] using h2
  · intro z
    refine ⟨(((fun j => (z j).out) : ∀ j, M j) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R), ?_⟩
    funext j
    have hm := QuotientGroup.eq.mp
      (QuotientGroup.out_eq' ((((fun j => (z j).out) : ∀ j, M j)) : (∀ j, M j) ⧸ Subgroup.pi Set.univ R))
    have hj := (Subgroup.mem_pi _).mp hm j (Set.mem_univ j)
    simp only [Pi.mul_apply, Pi.inv_apply] at hj
    show ((_ : M j) : M j ⧸ R j) = z j
    rw [← QuotientGroup.out_eq' (z j), QuotientGroup.eq]
    exact hj

/- English proof (translation)
Use `haveI : ∀ j, (rStab (v j)).FiniteIndex := fun j => ⟨hv j⟩`. Use `haveI : ∀ j, Fintype (M j ⧸ rStab (v j)) := fun j => Fintype.ofFinite _`. Set `S : Subgroup (∀ j, M j)` to `Subgroup.pi Set.univ (fun j => rStab (v j))`. Establish `hS : S ≤ rStab (fun x : (∀ j, M j) => ∏ j, v j (x j))`. Introduce `k hk`.

Rewrite using `[mem_rStab_iff_forall_mul_right_invariant]`. Introduce `x`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Conclude with `(mem_rStab_iff_forall_mul_right_invariant (v j) (k j)).mp ((Subgroup.mem_pi _).mp hk j (Set.mem_univ j)) (x j)`. Set `e` to `Equiv.ofBijective _ (bijective_pi_quotient_to_quotient_pi M (fun j => rStab (v j)))`.

Establish `hidx : S.index = ∏ j, (rStab (v j)).index`. Rewrite using `[Subgroup.index_eq_card, Nat.card_congr e, Nat.card_pi]`. Simplify using `only [Subgroup.index_eq_card]`. Establish `hS0 : S.index ≠ 0`. Rewrite using `[hidx]`.

Conclude with `Finset.prod_ne_zero_iff.mpr (fun j _ => hv j)`. Establish `hsum : (∑ᶠ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j)) = ∏ j, ∑ᶠ q : M j ⧸ rStab (v j), v j q.out`. Establish `h1 : ∀ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j) = ∏ j, v j ((e q j).out)`. Introduce `q`. Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations.

Conclude with `(apply_out (v j) (q.out j)).symm`. Rewrite using `[finsum_congr h1]`. Use `(finsum_comp_equiv e (f := fun z : (∀ j, M j ⧸ rStab (v j)) => ∏ j, v j (z j).out)).trans ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `only [finsum_eq_sum_of_fintype]`.

Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Rewrite using `[GlobalTheory.BCT.avg_eq_of_le_rStab _ _ S hS hS0]`. Simplify using `only [avg_eq_inv_index_mul_finsum_rStab_quotient]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Nat.cast_prod, ← hidx, hsum]`.
-/
theorem avg_pi {J : Type} [Fintype J] (M : J → Type) [∀ j, Group (M j)] (v : ∀ j, M j → ℂ)
    (hv : ∀ j, (rStab (v j)).index ≠ 0) :
    avg (fun x : (∀ j, M j) => ∏ j, v j (x j)) = ∏ j, avg (v j) := by
  classical
  haveI : ∀ j, (rStab (v j)).FiniteIndex := fun j => ⟨hv j⟩
  haveI : ∀ j, Fintype (M j ⧸ rStab (v j)) := fun j => Fintype.ofFinite _
  let S : Subgroup (∀ j, M j) := Subgroup.pi Set.univ (fun j => rStab (v j))
  have hS : S ≤ rStab (fun x : (∀ j, M j) => ∏ j, v j (x j)) := by
    intro k hk
    rw [mem_rStab_iff_forall_mul_right_invariant]
    intro x
    refine Finset.prod_congr rfl (fun j _ => ?_)
    exact (mem_rStab_iff_forall_mul_right_invariant (v j) (k j)).mp ((Subgroup.mem_pi _).mp hk j (Set.mem_univ j)) (x j)
  let e := Equiv.ofBijective _ (bijective_pi_quotient_to_quotient_pi M (fun j => rStab (v j)))
  have hidx : S.index = ∏ j, (rStab (v j)).index := by
    rw [Subgroup.index_eq_card, Nat.card_congr e, Nat.card_pi]
    simp only [Subgroup.index_eq_card]
  have hS0 : S.index ≠ 0 := by
    rw [hidx]; exact Finset.prod_ne_zero_iff.mpr (fun j _ => hv j)
  have hsum : (∑ᶠ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j)) = ∏ j, ∑ᶠ q : M j ⧸ rStab (v j), v j q.out := by
    have h1 : ∀ q : (∀ j, M j) ⧸ S, ∏ j, v j (q.out j) = ∏ j, v j ((e q j).out) := by
      intro q
      refine Finset.prod_congr rfl (fun j _ => ?_)
      exact (apply_out (v j) (q.out j)).symm
    rw [finsum_congr h1]
    refine (finsum_comp_equiv e (f := fun z : (∀ j, M j ⧸ rStab (v j)) => ∏ j, v j (z j).out)).trans ?_
    rw [finsum_eq_sum_of_fintype]
    simp only [finsum_eq_sum_of_fintype]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [GlobalTheory.BCT.avg_eq_of_le_rStab _ _ S hS hS0]
  simp only [avg_eq_inv_index_mul_finsum_rStab_quotient]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← Nat.cast_prod, ← hidx, hsum]

/- English proof (translation)
Introduce `ι G _ H _ p K KH hK u happ hu h1`. Establish `hs` using `Filter.eventually_cofinite.mp h1`. Set `T` to `hs.toFinset`. Set `π : K →* ∀ j : T, KH j` to `MonoidHom.pi (fun j : T => ((p j).comp K.subtype).codRestrict (KH j) (fun k => (hK k).1 k.2 j))`. Establish `hπ : Function.Surjective π`.

Introduce `y`. Set `y' : ∀ i, H i` to `fun i => if h : i ∈ T then ((y ⟨i, h⟩ : KH i) : H i) else 1`. Establish `hy' : ∀ i, y' i ∈ KH i`. Introduce `i`. Simplify using `only [y']`.

Use `split_ifs with h`. Conclude with `(y ⟨i, h⟩).2`. Conclude with `(KH i).one_mem`. Take `⟨x, hx⟩` from `happ y' (Filter.Eventually.of_forall hy')`. Establish `hxK : x ∈ K` using `(hK x).2 (fun i => by rw [hx i]; exact hy' i)`.

Use `⟨⟨x, hxK⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `p (j : ι) x = ((y j : KH (j : ι)) : H (j : ι))`. Rewrite using `[hx]`.

Simplify using `[y', j.2]`. Establish `hfun : (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) = (fun y : (∀ j : T, KH j) => ∏ j : T, u j (y j)) ∘ π`. Use function extensionality and compare the values at `k`. Rewrite using `[Function.comp_apply, finprod_eq_prod_of_mulSupport_subset _ (s := T)]`. Conclude with `(Finset.prod_coe_sort T (fun i => u i ⟨p i k, (hK k).1 k.2 i⟩)).symm`.

Introduce `i hi`. Simplify using `only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Introduce `hall`. Conclude with `(Function.mem_mulSupport.mp hi) (hall _)`. Rewrite using `[hfun, avg_comp_surj π hπ]`.

Use `(avg_pi (fun j : T => (KH j : Type)) (fun j => u j) (fun j => hu j)).trans ?_` and prove the remaining obligations. Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ (s := T)]`. Conclude with `Finset.prod_coe_sort T (fun i => avg (u i))`. Introduce `i hi`. Simplify using `only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]`.

Introduce `hall`. Apply `Function.mem_mulSupport.mp hi` to reduce the goal to its premises. Establish `hc : u i = fun _ => 1` using `funext hall`. Rewrite using `[hc]`. Conclude with `(GlobalTheory.AvgLin.avg_linear_translate_const _ (u i) (u i) 1 1 (hu i) (hu i)).2.2.2`.
-/
theorem avg_restrProd : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (K : Subgroup G) (KH : ∀ i, Subgroup (H i)) (hK : ∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) (u : ∀ i, KH i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ i, (rStab (u i)).index ≠ 0) → (∀ᶠ i in cofinite, ∀ k, u i k = 1) → avg (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) = ∏ᶠ i, avg (u i) := by
  intro ι G _ H _ p K KH hK u happ hu h1
  classical
  have hs := Filter.eventually_cofinite.mp h1
  let T := hs.toFinset
  let π : K →* ∀ j : T, KH j :=
    MonoidHom.pi (fun j : T => ((p j).comp K.subtype).codRestrict (KH j) (fun k => (hK k).1 k.2 j))
  have hπ : Function.Surjective π := by
    intro y
    let y' : ∀ i, H i := fun i => if h : i ∈ T then ((y ⟨i, h⟩ : KH i) : H i) else 1
    have hy' : ∀ i, y' i ∈ KH i := by
      intro i
      simp only [y']
      split_ifs with h
      · exact (y ⟨i, h⟩).2
      · exact (KH i).one_mem
    obtain ⟨x, hx⟩ := happ y' (Filter.Eventually.of_forall hy')
    have hxK : x ∈ K := (hK x).2 (fun i => by rw [hx i]; exact hy' i)
    refine ⟨⟨x, hxK⟩, ?_⟩
    funext j
    apply Subtype.ext
    change p (j : ι) x = ((y j : KH (j : ι)) : H (j : ι))
    rw [hx]
    simp [y', j.2]
  have hfun : (fun k : K => ∏ᶠ i, u i ⟨p i k, (hK k).1 k.2 i⟩) =
      (fun y : (∀ j : T, KH j) => ∏ j : T, u j (y j)) ∘ π := by
    funext k
    rw [Function.comp_apply, finprod_eq_prod_of_mulSupport_subset _ (s := T)]
    · exact (Finset.prod_coe_sort T (fun i => u i ⟨p i k, (hK k).1 k.2 i⟩)).symm
    · intro i hi
      simp only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro hall
      exact (Function.mem_mulSupport.mp hi) (hall _)
  rw [hfun, avg_comp_surj π hπ]
  refine (avg_pi (fun j : T => (KH j : Type)) (fun j => u j) (fun j => hu j)).trans ?_
  rw [finprod_eq_prod_of_mulSupport_subset _ (s := T)]
  · exact Finset.prod_coe_sort T (fun i => avg (u i))
  · intro i hi
    simp only [Finset.mem_coe, T, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro hall
    apply Function.mem_mulSupport.mp hi
    have hc : u i = fun _ => 1 := funext hall
    rw [hc]
    exact (GlobalTheory.AvgLin.avg_linear_translate_const _ (u i) (u i) 1 1 (hu i) (hu i)).2.2.2

end GlobalTheory.AvgRestr

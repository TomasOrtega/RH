import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LevelOfPairing

section Abstract

variable {G U : Type} [Group G] [CommGroup U] {R : G → G → U → Prop} {M : ℕ}

/- English proof (translation)
Use `List.prod_induction (fun y => y ^ M = 1) (fun x y hx hy => ?_) (one_pow _) fun z hz => ?_` and prove the remaining obligations. Rewrite using `[(cm x y).mul_pow, hx, hy, _root_.mul_one]`. Take `⟨i, rfl⟩` from `(List.mem_ofFn' _ _).1 hz`. Rewrite using `[← pow_mul, Nat.mul_comm, pow_mul, hy, one_pow]`.
-/
theorem prod_pow_eq_one (cm : ∀ a b : G, Commute a b) {n : ℕ} (y : Fin n → G) (hy : ∀ i, y i ^ M = 1)
    (a : Fin n → ℕ) : (List.ofFn fun i => y i ^ a i).prod ^ M = 1 := by
  refine List.prod_induction (fun y => y ^ M = 1) (fun x y hx hy => ?_) (one_pow _) fun z hz => ?_
  · rw [(cm x y).mul_pow, hx, hy, _root_.mul_one]
  · obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hz
    rw [← pow_mul, Nat.mul_comm, pow_mul, hy, one_pow]

/- English proof (translation)
Take `⟨c, hc, hc'⟩` from `hu 1 y (one_pow _) hy`. Establish `h` using `hm _ _ _ _ _ hc hc`. Rewrite `h` using `[_root_.mul_one]`. Establish `e : c * c = c` using `hc' _ h`. Establish `: c = 1` using `by simpa using e`.

Conclude with `this ▸ hc`.
-/
theorem rel_one (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {y : G} (hy : y ^ M = 1) :
    R 1 y 1 := by
  obtain ⟨c, hc, hc'⟩ := hu 1 y (one_pow _) hy
  have h := hm _ _ _ _ _ hc hc
  rw [_root_.mul_one] at h
  have e : c * c = c := hc' _ h
  have : c = 1 := by simpa using e
  exact this ▸ hc

/- English proof (translation)
Proceed by induction on `a with`. Consider the case `zero => simpa using h₁`. Consider the case `succ a ih => rw [pow_succ, pow_succ]`. Conclude with `hm _ _ _ _ _ ih h`.
-/
theorem rel_pow (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {x y : G} {c : U}
    (h₁ : R 1 y 1) (h : R x y c) (a : ℕ) : R (x ^ a) y (c ^ a) := by
  induction a with
  | zero => simpa using h₁
  | succ a ih => rw [pow_succ, pow_succ]; exact hm _ _ _ _ _ ih h

/- English proof (translation)
The claim follows from `| 0, _, _, _ => by simpa using h₁ | n + 1, x, c, h => by rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ] exact hm _ _ _ _ _ (h 0) (rel_prod hm h₁ _ _ fun i => h i.succ)`.
-/
theorem rel_prod (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {y : G}
    (h₁ : R 1 y 1) : ∀ {n : ℕ} (x : Fin n → G) (c : Fin n → U), (∀ i, R (x i) y (c i)) →
      R (List.ofFn x).prod y (∏ i, c i)
  | 0, _, _, _ => by simpa using h₁
  | n + 1, x, c, h => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    exact hm _ _ _ _ _ (h 0) (rel_prod hm h₁ _ _ fun i => h i.succ)

/- English proof (translation)
Establish `hi` using `i.2`. Distinguish the cases in `h : (i : ℕ) < g`. Use `⟨⟨i + g, by omega⟩, Or.inl (by simp [stdSymp, h]), fun i' hi' => ?_⟩` and prove the remaining obligations. Establish `: (i' : ℕ) ≠ i` using `fun e => hi' (Fin.ext e)`. Use `i'.2` as an intermediate fact.

Unfold `stdSymp`. Rewrite using `[if_neg (by simp only; omega), if_neg (by simp only; omega)]`. Use `⟨⟨i - g, by omega⟩, Or.inr ?_, fun i' hi' => ?_⟩` and prove the remaining obligations. Unfold `stdSymp`. Rewrite using `[if_neg (by simp only; omega), if_pos (by simp only; omega)]`.

Establish `: (i' : ℕ) ≠ i` using `fun e => hi' (Fin.ext e)`. Use `i'.2` as an intermediate fact. Unfold `stdSymp`. Rewrite using `[if_neg (by simp only; omega), if_neg (by simp only; omega)]`.
-/
theorem exists_column (g : ℕ) (i : Fin (2 * g)) :
    ∃ j : Fin (2 * g), (stdSymp g i j = 1 ∨ stdSymp g i j = -1) ∧ ∀ i', i' ≠ i → stdSymp g i' j = 0 := by
  have hi := i.2
  by_cases h : (i : ℕ) < g
  · refine ⟨⟨i + g, by omega⟩, Or.inl (by simp [stdSymp, h]), fun i' hi' => ?_⟩
    have : (i' : ℕ) ≠ i := fun e => hi' (Fin.ext e)
    have := i'.2
    unfold stdSymp
    rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]
  · refine ⟨⟨i - g, by omega⟩, Or.inr ?_, fun i' hi' => ?_⟩
    · unfold stdSymp
      rw [if_neg (by simp only; omega), if_pos (by simp only; omega)]
    · have : (i' : ℕ) ≠ i := fun e => hi' (Fin.ext e)
      have := i'.2
      unfold stdSymp
      rw [if_neg (by simp only; omega), if_neg (by simp only; omega)]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Take `⟨j, hj, hj'⟩` from `exists_column g i`. Establish `h₁` using `rel_one hu hm (hy j)`. Establish `key : ∀ a : Fin (2 * g) → Fin M, R (List.ofFn fun i => y i ^ (a i : ℕ)).prod (y j) ((ζ ^ stdSymp g i j) ^ (a i : ℕ))` using `fun a => by`. Establish `h` using `rel_prod hm h₁ (fun i => y i ^ (a i : ℕ)) (fun i => (ζ ^ stdSymp g i j) ^ (a i : ℕ)) fun i => rel_pow hm h₁ (hp i j) _`.

Rewrite `h` using `[Finset.prod_eq_single i (fun b _ hb => by rw [hj' b hb, zpow_zero, one_pow]) (fun h => absurd (Finset.mem_univ _) h)]`. Then use the resulting hypothesis. Establish `k₁` using `key c`. Rewrite `k₁` using `[e]`. Establish `q` using `(hu _ _ (prod_pow_eq_one cm y hy _) (hy j)).unique k₁ (key c')`. Establish `hζ' : IsPrimitiveRoot (ζ ^ stdSymp g i j) M`.

Break down `hj with hj | hj` into its components or cases. Rewrite using `[hj, zpow_one]` and apply the resulting hypothesis. Rewrite using `[hj, zpow_neg, zpow_one]`. Conclude with `hζ.inv`. Conclude with `Fin.ext (hζ'.pow_inj (c i).2 (c' i).2 q)`.
-/
theorem injective_comb (cm : ∀ a b : G, Commute a b)
    (hu : ∀ x y : G, x ^ M = 1 → y ^ M = 1 → ∃! c, R x y c)
    (hm : ∀ x x' y c c', R x y c → R x' y c' → R (x * x') y (c * c')) {ζ : U} (hζ : IsPrimitiveRoot ζ M)
    {g : ℕ} (y : Fin (2 * g) → G) (hy : ∀ i, y i ^ M = 1) (hp : ∀ i j, R (y i) (y j) (ζ ^ stdSymp g i j))
    (c c' : Fin (2 * g) → Fin M)
    (e : (List.ofFn fun i => y i ^ (c i : ℕ)).prod = (List.ofFn fun i => y i ^ (c' i : ℕ)).prod) : c = c' := by
  funext i
  obtain ⟨j, hj, hj'⟩ := exists_column g i
  have h₁ := rel_one hu hm (hy j)
  have key : ∀ a : Fin (2 * g) → Fin M,
      R (List.ofFn fun i => y i ^ (a i : ℕ)).prod (y j) ((ζ ^ stdSymp g i j) ^ (a i : ℕ)) := fun a => by
    have h := rel_prod hm h₁ (fun i => y i ^ (a i : ℕ)) (fun i => (ζ ^ stdSymp g i j) ^ (a i : ℕ))
      fun i => rel_pow hm h₁ (hp i j) _
    rwa [Finset.prod_eq_single i (fun b _ hb => by rw [hj' b hb, zpow_zero, one_pow])
      (fun h => absurd (Finset.mem_univ _) h)] at h
  have k₁ := key c
  rw [e] at k₁
  have q := (hu _ _ (prod_pow_eq_one cm y hy _) (hy j)).unique k₁ (key c')
  have hζ' : IsPrimitiveRoot (ζ ^ stdSymp g i j) M := by
    rcases hj with hj | hj
    · rwa [hj, zpow_one]
    · rw [hj, zpow_neg, zpow_one]; exact hζ.inv
  exact Fin.ext (hζ'.pow_inj (c i).2 (c' i).2 q)

/- English proof (translation)
Set `f : (Fin n → Fin M) → {x : G // x ^ M = 1}` to `fun c => ⟨_, prod_pow_eq_one cm y hy fun i => (c i : ℕ)⟩`. Establish `: Finite {x : G // x ^ M = 1}` using `Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hM)`. Establish `hb : Function.Bijective f`. Rewrite using `[Nat.bijective_iff_injective_and_card]`. Conclude with `⟨fun c c' h => hinj c c' (congrArg Subtype.val h), by rw [hcard]; simp⟩`.

Take `⟨c, hc⟩` from `hb.2 ⟨z, hz⟩`. Conclude with `⟨c, congrArg Subtype.val hc⟩`.
-/
theorem surjective_comb (cm : ∀ a b : G, Commute a b) (hM : M ≠ 0) {n : ℕ} (y : Fin n → G)
    (hy : ∀ i, y i ^ M = 1) (hcard : Nat.card {x : G // x ^ M = 1} = M ^ n)
    (hinj : ∀ c c' : Fin n → Fin M,
      (List.ofFn fun i => y i ^ (c i : ℕ)).prod = (List.ofFn fun i => y i ^ (c' i : ℕ)).prod → c = c')
    (z : G) (hz : z ^ M = 1) : ∃ c : Fin n → Fin M, (List.ofFn fun i => y i ^ (c i : ℕ)).prod = z := by
  let f : (Fin n → Fin M) → {x : G // x ^ M = 1} := fun c => ⟨_, prod_pow_eq_one cm y hy fun i => (c i : ℕ)⟩
  have : Finite {x : G // x ^ M = 1} := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hM)
  have hb : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨fun c c' h => hinj c c' (congrArg Subtype.val h), by rw [hcard]; simp⟩
  obtain ⟨c, hc⟩ := hb.2 ⟨z, hz⟩
  exact ⟨c, congrArg Subtype.val hc⟩

end Abstract

end GlobalTheory.LevelOfPairing

namespace GlobalTheory

open LevelOfPairing in

/- English proof (translation)
Introduce `hG hW hN S _ P M ze hze hK x hx hp`. Use `P.isAb.comm` as an intermediate fact. Establish `cm : ∀ (T : Over S) (a b : T ⟶ P.A), Commute a b` using `fun T a b => _root_.mul_comm a b`. Establish `tor : ∀ (T : Over S) (h : T ⟶ baseOver S) (i), (h ≫ x i) ^ M = 1` using `fun T h i => by`. Rewrite using `[← MonObj.comp_pow, hx, MonObj.comp_one]`.

Establish `ind : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (c c' : Fin (2 * P.g) → Fin M), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ x i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ x i) (fun i => (c …`. Introduce `K _ s c c' e`. Take `⟨hu, hm, -⟩` from `hW S P M (Over.mk s)`. Use `injective_comb (R := fun a b u => WeilIs P.A P.L M a b u) (cm _) hu hm (hK K s).2 _ (tor _ _) (fun i j => ?_) c c' e` and prove the remaining obligations. Establish `h` using `CommPairing.weilIs_pull hG P.isAb P.isLB (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) (hp i j)`.

Conclude with `(map_zpow (Units.map s.appTop.hom.toMonoidHom) ze _) ▸ h`. Use `⟨⟨x, hze, hx, fun K _ _ s => ind K s, fun K _ _ s z hz => ?_, hp⟩, rfl⟩` and prove the remaining obligations. Establish `hM : M ≠ 0` using `fun e => (hK K s).1 (by rw [e, Nat.cast_zero])`. Conclude with `surjective_comb (cm _) hM _ (tor _ _) ((hN S P M (Nat.one_le_iff_ne_zero.2 hM)).2.2.2.2 K s (hK K s).1) (ind K s) z hz`.
-/
theorem exists_level_of_pairing : GlobalFnsSt → WeilSt → MulNSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (M : ℕ) (ze : Γ(S, ⊤)ˣ), IsPrimitiveRoot ze M → (∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S), (M : K) ≠ 0 ∧ IsPrimitiveRoot (Units.map s.appTop.hom.toMonoidHom ze) M) → ∀ x : Fin (2 * P.g) → (baseOver S ⟶ P.A), (∀ i, x i ^ M = 1) → (∀ i j, WeilIs P.A P.L M (x i) (x j) (ze ^ stdSymp P.g i j)) → ∃ lev : Level P M ze, lev.pt = x := by
  intro hG hW hN S _ P M ze hze hK x hx hp
  have := P.isAb.comm
  have cm : ∀ (T : Over S) (a b : T ⟶ P.A), Commute a b := fun T a b => _root_.mul_comm a b
  have tor : ∀ (T : Over S) (h : T ⟶ baseOver S) (i), (h ≫ x i) ^ M = 1 := fun T h i => by
    rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  have ind : ∀ (K : Type) [Field K] (s : Spec (CommRingCat.of K) ⟶ S) (c c' : Fin (2 * P.g) → Fin M),
      linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ x i) (fun i => (c i : ℕ)) =
        linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) ≫ x i) (fun i => (c' i : ℕ)) →
      c = c' := by
    intro K _ s c c' e
    obtain ⟨hu, hm, -⟩ := hW S P M (Over.mk s)
    refine injective_comb (R := fun a b u => WeilIs P.A P.L M a b u) (cm _) hu hm (hK K s).2 _
      (tor _ _) (fun i j => ?_) c c' e
    have h := CommPairing.weilIs_pull hG P.isAb P.isLB
      (Over.homMk s (by simp) : Over.mk s ⟶ baseOver S) (hp i j)
    exact (map_zpow (Units.map s.appTop.hom.toMonoidHom) ze _) ▸ h
  refine ⟨⟨x, hze, hx, fun K _ _ s => ind K s, fun K _ _ s z hz => ?_, hp⟩, rfl⟩
  have hM : M ≠ 0 := fun e => (hK K s).1 (by rw [e, Nat.cast_zero])
  exact surjective_comb (cm _) hM _ (tor _ _)
    ((hN S P M (Nat.one_le_iff_ne_zero.2 hM)).2.2.2.2 K s (hK K s).1) (ind K s) z hz

end GlobalTheory

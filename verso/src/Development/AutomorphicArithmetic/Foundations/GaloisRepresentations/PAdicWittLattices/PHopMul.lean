import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

/- English proof (translation)
Use `Eq.trans (finsum_congr fun z => ?_) (finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (G ⧸ K)) (f := fun w : G ⧸ K => f' (g⁻¹ * w.out) • Φ w.out))` and prove the remaining obligations. Establish `e : (MulAction.toPerm g : Equiv.Perm (G ⧸ K)) z = ((g * z.out : G) : G ⧸ K)`. Rewrite using `[MulAction.toPerm_apply]`. Use `conv_lhs => rw [← QuotientGroup.out_eq' z]`. Both sides reduce to the same expression.

Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K (g * z.out)`. Simplify using `only [e, hk]`. Rewrite using `[show g⁻¹ * (g * z.out * (k : G)) = z.out * k by group, hf' _ k.2, hΦ _ k.2]`.
-/
private theorem sum_translate {G R M : Type*} [Group G] [Field R] [AddCommGroup M] [Module R M]
    (K : Subgroup G) (f' : G → R) (Φ : G → M) (hf' : ∀ k ∈ K, ∀ g, f' (g * k) = f' g)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (g : G) :
    ∑ᶠ z : G ⧸ K, f' z.out • Φ (g * z.out) = ∑ᶠ w : G ⧸ K, f' (g⁻¹ * w.out) • Φ w.out := by
  refine Eq.trans (finsum_congr fun z => ?_)
    (finsum_comp_equiv (MulAction.toPerm g : Equiv.Perm (G ⧸ K))
      (f := fun w : G ⧸ K => f' (g⁻¹ * w.out) • Φ w.out))
  have e : (MulAction.toPerm g : Equiv.Perm (G ⧸ K)) z = ((g * z.out : G) : G ⧸ K) := by
    rw [MulAction.toPerm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' z]
    rfl
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (g * z.out)
  simp only [e, hk]
  rw [show g⁻¹ * (g * z.out * (k : G)) = z.out * k by group, hf' _ k.2, hΦ _ k.2]

/- English proof (translation)
Set `Tw : Finset (G ⧸ K)` to `sf.toFinset.biUnion fun y => sf'.toFinset.image fun z => y.out • z`. Establish `hT : ∀ y ∈ sf.toFinset, ∀ w : G ⧸ K, f' (y.out⁻¹ * w.out) ≠ 0 → w ∈ Tw`. Introduce `y hy w hw`. Use `Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨((y.out⁻¹ * w.out : G) : G ⧸ K), ?_, ?_⟩⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `QuotientGroup.mk_out_eq_mul K (y.out⁻¹ * w.out)`.

Simplify using `only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]`. Rewrite using `[hk, hf' _ k.2]`. Conclude with `hw`. Use `show ((y.out * (y.out⁻¹ * w.out) : G) : G ⧸ K) = w`. Rewrite using `[mul_inv_cancel_left, QuotientGroup.out_eq']`.

Establish `hin : ∀ y ∈ sf.toFinset, ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out = ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out`. Introduce `y hy`. Use `finsum_eq_sum_of_support_subset _ fun w hw => ?_` and prove the remaining obligations. Use `hT y hy w fun h => hw ?_` and prove the remaining obligations. Simplify using `[h]`.

Establish `hc : ∀ w : G ⧸ K, conv K f f' w.out = ∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out)`. Introduce `w`. Use `finsum_eq_sum_of_support_subset _ fun y hy => ?_` and prove the remaining obligations. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]`. Introduce `h`.

Conclude with `hy (by simp [h])`. Establish `hl : ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) = ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out`. Use `(finsum_congr fun y => by rw [sum_translate K f' Φ hf' hΦ y.out]).trans ?_` and prove the remaining obligations. Use `finsum_eq_sum_of_support_subset _ fun y hy => ?_` and prove the remaining obligations. Simplify using `only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]`.

Introduce `h`. Conclude with `hy (by simp [h])`. Establish `hs : Function.support (fun w : G ⧸ K => conv K f f' w.out • Φ w.out) ⊆ (Tw : Set (G ⧸ K))`. Introduce `w hw`. Establish `h0 : conv K f f' w.out ≠ 0` using `fun h => hw (by simp [h])`.

Rewrite `h0` using `[hc w]`. Take `⟨y, hy, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h0`. Conclude with `Finset.mem_coe.2 (hT y hy w (right_ne_zero_of_mul hne))`. Rewrite using `[hl, finsum_eq_sum_of_support_subset _ hs]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.smul_sum, Finset.sum_smul, mul_smul]`. Conclude with `Finset.sum_comm`. Use `_ = ∑ w ∈ Tw, conv K f f' w.out • Φ w.out := Finset.sum_congr rfl fun w _ => by rw [hc w]`.
-/
private theorem sum_conv {G R : Type} {M : Type*} [Group G] [Field R] [AddCommGroup M] [Module R M]
    (K : Subgroup G) (f f' : G → R) (Φ : G → M) (hf' : ∀ k ∈ K, ∀ g, f' (g * k) = f' g)
    (hΦ : ∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) (sf : {y : G ⧸ K | f y.out ≠ 0}.Finite)
    (sf' : {y : G ⧸ K | f' y.out ≠ 0}.Finite) :
    ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) =
      ∑ᶠ w : G ⧸ K, conv K f f' w.out • Φ w.out := by
  classical
  let Tw : Finset (G ⧸ K) := sf.toFinset.biUnion fun y => sf'.toFinset.image fun z => y.out • z
  have hT : ∀ y ∈ sf.toFinset, ∀ w : G ⧸ K, f' (y.out⁻¹ * w.out) ≠ 0 → w ∈ Tw := by
    intro y hy w hw
    refine Finset.mem_biUnion.2 ⟨y, hy, Finset.mem_image.2 ⟨((y.out⁻¹ * w.out : G) : G ⧸ K), ?_, ?_⟩⟩
    · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (y.out⁻¹ * w.out)
      simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rw [hk, hf' _ k.2]
      exact hw
    · show ((y.out * (y.out⁻¹ * w.out) : G) : G ⧸ K) = w
      rw [mul_inv_cancel_left, QuotientGroup.out_eq']
  have hin : ∀ y ∈ sf.toFinset, ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out =
      ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out := by
    intro y hy
    refine finsum_eq_sum_of_support_subset _ fun w hw => ?_
    refine hT y hy w fun h => hw ?_
    simp [h]
  have hc : ∀ w : G ⧸ K, conv K f f' w.out = ∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out) := by
    intro w
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    exact hy (by simp [h])
  have hl : ∑ᶠ y : G ⧸ K, f y.out • ∑ᶠ z : G ⧸ K, f' z.out • Φ (y.out * z.out) =
      ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out := by
    refine (finsum_congr fun y => by rw [sum_translate K f' Φ hf' hΦ y.out]).trans ?_
    refine finsum_eq_sum_of_support_subset _ fun y hy => ?_
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h
    exact hy (by simp [h])
  have hs : Function.support (fun w : G ⧸ K => conv K f f' w.out • Φ w.out) ⊆ (Tw : Set (G ⧸ K)) := by
    intro w hw
    have h0 : conv K f f' w.out ≠ 0 := fun h => hw (by simp [h])
    rw [hc w] at h0
    obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
    exact Finset.mem_coe.2 (hT y hy w (right_ne_zero_of_mul hne))
  rw [hl, finsum_eq_sum_of_support_subset _ hs]
  calc ∑ y ∈ sf.toFinset, f y.out • ∑ᶠ w : G ⧸ K, f' (y.out⁻¹ * w.out) • Φ w.out
      = ∑ y ∈ sf.toFinset, f y.out • ∑ w ∈ Tw, f' (y.out⁻¹ * w.out) • Φ w.out :=
        Finset.sum_congr rfl fun y hy => by rw [hin y hy]
    _ = ∑ w ∈ Tw, (∑ y ∈ sf.toFinset, f y.out * f' (y.out⁻¹ * w.out)) • Φ w.out := by
        simp only [Finset.smul_sum, Finset.sum_smul, mul_smul]
        exact Finset.sum_comm
    _ = ∑ w ∈ Tw, conv K f f' w.out • Φ w.out :=
        Finset.sum_congr rfl fun w _ => by rw [hc w]

/- English proof (translation)
Distinguish the cases in `a : X.admitted i j h`. Conclude with `X.pl_left T a hk x`. Establish `b : ¬ X.admitted i j (k * h)` using `fun b => a (by`. Simplify using `using b.mul (X.tower_admissible_self ((X.K j).inv_mem hk)))`. Simplify using `[Tower.pl, a, b]`.
-/
private theorem pl_left_all {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {R : Type} [Field R]
    (T : Th.{u} B R) {i j : X.ι} {k : G} (hk : k ∈ X.K j) (h : G) (x : T.H (X.q j)) :
    X.pl T i j (k * h) x = X.pl T i j h x := by
  by_cases a : X.admitted i j h
  · exact X.pl_left T a hk x
  · have b : ¬ X.admitted i j (k * h) := fun b => a (by
      simpa using b.mul (X.tower_admissible_self ((X.K j).inv_mem hk)))
    simp [Tower.pl, a, b]

end UpperTheory.Gal.G3

/- English proof (translation)
Introduce `hR hD hE B G _ X R _ _ T hT j f f' hf hf'`. Establish `hF : X.IsFn j (conv (X.K j) f f')` using `((hR X R j).2.2.1 f f' hf hf').2`. Establish `hA` using `(hE X T hT j f hf).1`. Establish `hA'` using `(hE X T hT j f' hf').1`. Use `((hE X T hT j _ hF).2 _ ?_).symm` and prove the remaining obligations.

Take `⟨m1, l1, a1⟩` from `(hD X T hT j f hf).1`. Take `⟨m2, l2, a2⟩` from `(hD X T hT j f' hf').1`. Take `⟨m3, l3, a3⟩` from `(hD X T hT j _ hF).1`. Set `S : Finset (X.ι × G)` to `{(m1, 1), (m2, 1), (m3, 1)} ∪ hf.2.2.toFinset.image fun y => (m2, y.out⁻¹)`. Take `⟨m, lm, -, hm⟩` from `X.deep j S`.

Establish `le1 : X.K m ≤ X.K m1` using `fun u hu => by simpa using hm (m1, 1) (by simp [S]) u hu`. Establish `le3 : X.K m ≤ X.K m3` using `fun u hu => by simpa using hm (m3, 1) (by simp [S]) u hu`. Establish `ad1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹` using `fun g hg => by`. Simplify using `using (X.isAdmissibleIntegralBasisChange_one le1).mul (a1 g hg)`. Establish `ad3 : ∀ g, conv (X.K j) f f' g ≠ 0 → X.admitted m j g⁻¹` using `fun g hg => by`.

Simplify using `using (X.isAdmissibleIntegralBasisChange_one le3).mul (a3 g hg)`. Use `(hD X T hT j _ hF).2 _ m lm ad3 fun x => ?_` and prove the remaining obligations. Establish `step : ∀ y : G ⧸ X.K j, f y.out • X.pl T m j y.out⁻¹ (X.hecke T j f' x) = f y.out • ∑ᶠ z : G ⧸ X.K j, f' z.out • X.pl T m j (y.out * z.out)⁻¹ x`. Introduce `y`. Distinguish the cases in `h : f y.out = 0`.

Simplify using `[h]`. Establish `ad : X.admitted m m2 y.out⁻¹` using `⟨hf.2.1 _ h, fun u hu => hm (m2, y.out⁻¹) (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, by simpa using h, rfl⟩)) u hu⟩`. Establish `e : X.pl T m j y.out⁻¹ (X.hecke T j f' x) = X.pl T m m2 y.out⁻¹ (X.pl T m2 j 1 (X.hecke T j f' x))`. Rewrite using `[X.pl_pl T ad (X.isAdmissibleIntegralBasisChange_one l2), one_mul]`. Establish `fin : (Function.support fun z : G ⧸ X.K j => f' z.out • X.pl T m2 j z.out⁻¹ x).Finite` using `hf'.2.2.subset fun z hz h0 => hz (by simp [h0])`.

Rewrite using `[e, hA' m2 l2 a2 x, map_finsum _ fin]`. Use `congr 1`. Use `finsum_congr fun z => ?_` and prove the remaining obligations. Distinguish the cases in `h' : f' z.out = 0`. Simplify using `[h']`.

Rewrite using `[map_smul, X.pl_pl T ad (a2 _ h'), mul_inv_rev]`. Rewrite using `[Module.End.mul_apply, hA m lm ad1, finsum_congr step]`. Conclude with `sum_conv (X.K j) f f' (fun g => X.pl T m j g⁻¹ x) (fun k hk g => (hf'.1 k hk g).2) (fun k hk g => by`. Simplify using `only [mul_inv_rev]`. Conclude with `pl_left_all X T ((X.K j).inv_mem hk) _ x) hf.2.2 hf'.2.2`.
-/
theorem UpperTheory.Gal.G3.pHopMul :
    FnRing → HopDeep.{u} → HopEx.{u} → HopMul.{u} := by
  intro hR hD hE B G _ X R _ _ T hT j f f' hf hf'
  have hF : X.IsFn j (conv (X.K j) f f') := ((hR X R j).2.2.1 f f' hf hf').2
  have hA := (hE X T hT j f hf).1
  have hA' := (hE X T hT j f' hf').1
  refine ((hE X T hT j _ hF).2 _ ?_).symm
  obtain ⟨m1, l1, a1⟩ := (hD X T hT j f hf).1
  obtain ⟨m2, l2, a2⟩ := (hD X T hT j f' hf').1
  obtain ⟨m3, l3, a3⟩ := (hD X T hT j _ hF).1
  classical
  let S : Finset (X.ι × G) :=
    {(m1, 1), (m2, 1), (m3, 1)} ∪ hf.2.2.toFinset.image fun y => (m2, y.out⁻¹)
  obtain ⟨m, lm, -, hm⟩ := X.deep j S
  have le1 : X.K m ≤ X.K m1 := fun u hu => by simpa using hm (m1, 1) (by simp [S]) u hu
  have le3 : X.K m ≤ X.K m3 := fun u hu => by simpa using hm (m3, 1) (by simp [S]) u hu
  have ad1 : ∀ g, f g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one le1).mul (a1 g hg)
  have ad3 : ∀ g, conv (X.K j) f f' g ≠ 0 → X.admitted m j g⁻¹ := fun g hg => by
    simpa using (X.isAdmissibleIntegralBasisChange_one le3).mul (a3 g hg)
  refine (hD X T hT j _ hF).2 _ m lm ad3 fun x => ?_
  have step : ∀ y : G ⧸ X.K j, f y.out • X.pl T m j y.out⁻¹ (X.hecke T j f' x) =
      f y.out • ∑ᶠ z : G ⧸ X.K j, f' z.out • X.pl T m j (y.out * z.out)⁻¹ x := by
    intro y
    by_cases h : f y.out = 0
    · simp [h]
    have ad : X.admitted m m2 y.out⁻¹ := ⟨hf.2.1 _ h, fun u hu => hm (m2, y.out⁻¹)
      (Finset.mem_union_right _ (Finset.mem_image.2 ⟨y, by simpa using h, rfl⟩)) u hu⟩
    have e : X.pl T m j y.out⁻¹ (X.hecke T j f' x) =
        X.pl T m m2 y.out⁻¹ (X.pl T m2 j 1 (X.hecke T j f' x)) := by
      rw [X.pl_pl T ad (X.isAdmissibleIntegralBasisChange_one l2), one_mul]
    have fin : (Function.support fun z : G ⧸ X.K j => f' z.out • X.pl T m2 j z.out⁻¹ x).Finite :=
      hf'.2.2.subset fun z hz h0 => hz (by simp [h0])
    rw [e, hA' m2 l2 a2 x, map_finsum _ fin]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases h' : f' z.out = 0
    · simp [h']
    rw [map_smul, X.pl_pl T ad (a2 _ h'), mul_inv_rev]
  rw [Module.End.mul_apply, hA m lm ad1, finsum_congr step]
  exact sum_conv (X.K j) f f' (fun g => X.pl T m j g⁻¹ x) (fun k hk g => (hf'.1 k hk g).2)
    (fun k hk g => by
      simp only [mul_inv_rev]
      exact pl_left_all X T ((X.K j).inv_mem hk) _ x) hf.2.2 hf'.2.2

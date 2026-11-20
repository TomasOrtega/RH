import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

/- English proof (translation)
Establish `key : ∀ {L : M → G}, (∀ a b, L (a + b) = L a * L b) → (∀ a, L a = 1 ↔ a ∈ W) → ∀ a b, L a = L b ↔ W.mkQ a = W.mkQ b`. Introduce `L hadd hker a b`. Establish `h : L a = L (a - b) * L b` using `by rw [← hadd, sub_add_cancel]`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hker, h]`. Prove the components needed by the constructor for the conclusion.

Introduce `e`. Conclude with `mul_right_cancel (e.trans (_root_.one_mul _).symm)`. Introduce `e`. Rewrite using `[e, _root_.one_mul]`. Establish `eq` using `key hadd hker`.

Use `choose z hz using hsurj`. Set `f₀ : M →ₗ[O] M ⧸ W` to `{ toFun := fun y => W.mkQ (z y) map_add' := fun a b => by`. Rewrite using `[← map_add, ← eq, hadd, hz, hz, hz, hadd']`. Use the proof step `map_smul' := fun c a => by`. Rewrite using `[RingHom.id_apply, ← LinearMap.map_smul, ← eq, hsm, hz, hz, hsm'] }`.

Establish `hf₀ : W ≤ LinearMap.ker f₀`. Introduce `y hy`. Rewrite using `[LinearMap.mem_ker]`. Use `show W.mkQ (z y) = 0`. Rewrite using `[← map_zero W.mkQ, ← eq, hz, (hker' y).2 hy, (hker 0).2 W.zero_mem]`.

Set `f` to `W.liftQ f₀ hf₀`. Establish `hf : ∀ y, f (W.mkQ y) = W.mkQ (z y)` using `fun y => rfl`. Establish `bij : Function.Bijective f`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `q hq`. Take `⟨y, rfl⟩` from `W.mkQ_surjective q`. Rewrite `hq` using `[hf, ← map_zero W.mkQ, ← eq, hz, (hker 0).2 W.zero_mem, hker']`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `hq`.

Introduce `q`. Take `⟨a, rfl⟩` from `W.mkQ_surjective q`. Take `⟨y, hy⟩` from `hsurj' a`. Conclude with `⟨W.mkQ y, by rw [hf, ← eq, hz, hy]⟩`. Use `⟨LinearEquiv.ofBijective f bij, ?_, ?_⟩` and prove the remaining obligations.

Introduce `y`. Rewrite using `[← hz y, eq, Function.surjInv_eq (Submodule.mkQ_surjective W)]`. Both sides reduce to the same expression. Introduce `g hg`. Use `LinearEquiv.ext fun q => ?_` and prove the remaining obligations.

Take `⟨y, rfl⟩` from `W.mkQ_surjective q`. Rewrite using `[LinearEquiv.ofBijective_apply, hf, ← Function.surjInv_eq (Submodule.mkQ_surjective W) (g (W.mkQ y)), ← eq, hg y, hz]`.
-/
theorem exists_unique_quotAut {O M G : Type*} [Ring O] [AddCommGroup M] [Module O M] [Group G]
    (W : Submodule O M) (act : O → G → G) (L L' : M → G)
    (hadd : ∀ a b, L (a + b) = L a * L b) (hadd' : ∀ a b, L' (a + b) = L' a * L' b)
    (hsm : ∀ (c : O) a, L (c • a) = act c (L a)) (hsm' : ∀ (c : O) a, L' (c • a) = act c (L' a))
    (hker : ∀ a, L a = 1 ↔ a ∈ W) (hker' : ∀ a, L' a = 1 ↔ a ∈ W)
    (hsurj : ∀ a, ∃ b, L b = L' a) (hsurj' : ∀ a, ∃ b, L' b = L a) :
    ∃! g : (M ⧸ W) ≃ₗ[O] (M ⧸ W),
      ∀ y, L (Function.surjInv (Submodule.mkQ_surjective W) (g (W.mkQ y))) = L' y := by
  have key : ∀ {L : M → G}, (∀ a b, L (a + b) = L a * L b) → (∀ a, L a = 1 ↔ a ∈ W) →
      ∀ a b, L a = L b ↔ W.mkQ a = W.mkQ b := by
    intro L hadd hker a b
    have h : L a = L (a - b) * L b := by rw [← hadd, sub_add_cancel]
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← hker, h]
    constructor
    · intro e
      exact mul_right_cancel (e.trans (_root_.one_mul _).symm)
    · intro e
      rw [e, _root_.one_mul]
  have eq := key hadd hker
  choose z hz using hsurj
  let f₀ : M →ₗ[O] M ⧸ W :=
    { toFun := fun y => W.mkQ (z y)
      map_add' := fun a b => by
        rw [← map_add, ← eq, hadd, hz, hz, hz, hadd']
      map_smul' := fun c a => by
        rw [RingHom.id_apply, ← LinearMap.map_smul, ← eq, hsm, hz, hz, hsm'] }
  have hf₀ : W ≤ LinearMap.ker f₀ := by
    intro y hy
    rw [LinearMap.mem_ker]
    show W.mkQ (z y) = 0
    rw [← map_zero W.mkQ, ← eq, hz, (hker' y).2 hy, (hker 0).2 W.zero_mem]
  let f := W.liftQ f₀ hf₀
  have hf : ∀ y, f (W.mkQ y) = W.mkQ (z y) := fun y => rfl
  have bij : Function.Bijective f := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro q hq
      obtain ⟨y, rfl⟩ := W.mkQ_surjective q
      rw [hf, ← map_zero W.mkQ, ← eq, hz, (hker 0).2 W.zero_mem, hker'] at hq
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hq
    · intro q
      obtain ⟨a, rfl⟩ := W.mkQ_surjective q
      obtain ⟨y, hy⟩ := hsurj' a
      exact ⟨W.mkQ y, by rw [hf, ← eq, hz, hy]⟩
  refine ⟨LinearEquiv.ofBijective f bij, ?_, ?_⟩
  · intro y
    rw [← hz y, eq, Function.surjInv_eq (Submodule.mkQ_surjective W)]
    rfl
  · intro g hg
    refine LinearEquiv.ext fun q => ?_
    obtain ⟨y, rfl⟩ := W.mkQ_surjective q
    rw [LinearEquiv.ofBijective_apply, hf, ← Function.surjInv_eq (Submodule.mkQ_surjective W) (g (W.mkQ y)),
      ← eq, hg y, hz]

/- English proof (translation)
Introduce `hl hl'`. Take `⟨hinj, hsur⟩` from `hl.2.2.2 k (𝟙 _)`. Take `⟨hinj', hsur'⟩` from `hl'.2.2.2 k (𝟙 _)`. Establish `canc : ∀ u v : Over.mk x ⟶ o.A, (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ u = (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ v → u = v`. Introduce `u v h`.

Use `ext`. Use `congrArg CommaMorphism.left h` as an intermediate fact. Simplify using `using this`. Establish `killed : ∀ (l₁ : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l₁ → ∀ a, ∀ c ∈ w0 ^ r, ((Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ l₁ a) ≫ o.act.act (algebraMap (𝓞 D.F) D.O c) = 1`. Introduce `l₁ h₁ a c hc`.

Rewrite using `[Category.assoc, ← h₁.2.1, h₁.2.2.1 _ (Submodule.subset_span ⟨c, hc, a, rfl⟩), comp_one]`. Conclude with `exists_unique_quotAut (wSub D w0 r) (fun c g => g ≫ o.act.act c) l l' hl.1 hl'.1 hl.2.1 hl'.2.1 (fun a => ⟨fun h => hinj a (by rw [h, comp_one]), fun h => hl.2.2.1 a h⟩) (fun a => ⟨fun h => hinj' a (by rw [h, comp_one]), fun h => hl'.2.2.1 a h⟩) (fun a => by`. Take `⟨y, hy⟩` from `hsur _ (killed l' hl' a)`. Conclude with `⟨y, canc _ _ hy⟩)`. Use the proof step `(fun a => by`.

Take `⟨y, hy⟩` from `hsur' _ (killed l hl a)`. Conclude with `⟨y, canc _ _ hy⟩)`.
-/
theorem etLev_rel_existsUnique (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (w0 : Ideal (𝓞 D.F)) (r : ℕ) (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S) (l l' : D.La → (Over.mk x ⟶ o.A)) :
    IsEtLevOver o w0 r l → IsEtLevOver o w0 r l' → ∃! g : LevGrp D w0 r, ∀ y, l (levAct g y) = l' y := by
  intro hl hl'
  obtain ⟨hinj, hsur⟩ := hl.2.2.2 k (𝟙 _)
  obtain ⟨hinj', hsur'⟩ := hl'.2.2.2 k (𝟙 _)
  have canc : ∀ u v : Over.mk x ⟶ o.A,
      (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ u =
        (Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ v → u = v := by
    intro u v h
    ext
    have := congrArg CommaMorphism.left h
    simpa using this
  have killed : ∀ (l₁ : D.La → (Over.mk x ⟶ o.A)), IsEtLevOver o w0 r l₁ → ∀ a, ∀ c ∈ w0 ^ r,
      ((Over.homMk (𝟙 _) rfl : Over.mk (𝟙 (Sp k) ≫ (Over.mk x).hom) ⟶ Over.mk x) ≫ l₁ a) ≫
        o.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := by
    intro l₁ h₁ a c hc
    rw [Category.assoc, ← h₁.2.1, h₁.2.2.1 _ (Submodule.subset_span ⟨c, hc, a, rfl⟩), comp_one]
  exact exists_unique_quotAut (wSub D w0 r) (fun c g => g ≫ o.act.act c) l l' hl.1 hl'.1 hl.2.1 hl'.2.1
    (fun a => ⟨fun h => hinj a (by rw [h, comp_one]), fun h => hl.2.2.1 a h⟩)
    (fun a => ⟨fun h => hinj' a (by rw [h, comp_one]), fun h => hl'.2.2.1 a h⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur _ (killed l' hl' a)
      exact ⟨y, canc _ _ hy⟩)
    (fun a => by
      obtain ⟨y, hy⟩ := hsur' _ (killed l hl a)
      exact ⟨y, canc _ _ hy⟩)

end GlobalTheory.UPel.HT.EtLev

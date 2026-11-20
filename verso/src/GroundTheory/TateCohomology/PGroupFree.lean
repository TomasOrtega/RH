import Mathlib
import GroundTheory.TateCohomology.InducedNorm
import GroundTheory.TateCohomology.TateAddEquivAbelianizationTateClass
import GroundTheory.TateCohomology.PGroupFixed
set_option maxSynthPendingDepth 1

namespace GroundTheory.GroupCoh

open CategoryTheory Limits groupHomology Representation Finsupp
open scoped MonoidAlgebra

universe u

section Naturality

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G} (f : A ⟶ B)

/- English proof (translation)
Proceed by induction on `y using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Consider the case `single g a`. Rewrite using `[Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₁₀_single, d₁₀_single, map_sub, Rep.hom_comm_apply]`.

Both sides reduce to the same expression.
-/
theorem d₁₀_mapRange (y : G →₀ A) :
    d₁₀ B (Finsupp.mapRange.linearMap f.hom.toLinearMap y) = f.hom (d₁₀ A y) := by
  induction y using Finsupp.induction_linear with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₁₀_single, d₁₀_single,
      map_sub, Rep.hom_comm_apply]
    rfl

/- English proof (translation)
Proceed by induction on `c using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Consider the case `single g a`. Rewrite using `[Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₂₁_single, d₂₁_single, map_add, map_sub, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapRange_single, Finsupp.mapRange_single, s …`.
-/
theorem d₂₁_mapRange (c : G × G →₀ A) :
    d₂₁ B (Finsupp.mapRange.linearMap f.hom.toLinearMap c) =
      Finsupp.mapRange.linearMap f.hom.toLinearMap (d₂₁ A c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single g a =>
    rw [Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, d₂₁_single, d₂₁_single,
      map_add, map_sub, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange.linearMap_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Finsupp.mapRange_single,
      Finsupp.mapRange_single,
      show f.hom.toLinearMap (A.ρ g.1⁻¹ a) = B.ρ g.1⁻¹ (f.hom.toLinearMap a) from
        Rep.hom_comm_apply f g.1⁻¹ a]

end Naturality

section Chains

variable {k G : Type u} [CommRing k] [Group G] {A B : Rep.{u} k G}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(Finsupp.lsum k fun g => A.ρ g⁻¹ - LinearMap.id) z = _`. Rewrite using `[Finsupp.lsum_apply, Finsupp.sum]`. Both sides reduce to the same expression.
-/
theorem d₁₀_apply_eq_sum (z : G →₀ A) :
    d₁₀ A z = ∑ g ∈ z.support, (A.ρ g⁻¹ (z g) - z g) := by
  change (Finsupp.lsum k fun g => A.ρ g⁻¹ - LinearMap.id) z = _
  rw [Finsupp.lsum_apply, Finsupp.sum]
  rfl

/- English proof (translation)
Establish `hsurj' : Function.Surjective f.hom.toLinearMap` using `hsurj`. Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : x ∈ LinearMap.range (d₁₀ A).hom := by`. Rewrite using `[range_d₁₀_eq_coinvariantsKer]`. Conclude with `hxI`. Set `L` to `Finsupp.mapRange.linearMap (α := G) f.hom.toLinearMap`.

Establish `hY : L y ∈ cycles₁ B`. Express the relevant statement in the definitionally equal form `d₁₀ B (L y) = 0`. Rewrite using `[d₁₀_mapRange f y]`. Express the relevant statement in the definitionally equal form `f.hom (d₁₀ A y) = 0`. Rewrite using `[show d₁₀ A y = x from hy]`.

Conclude with `hx`. Establish `h0 : H1π B ⟨L y, hY⟩ = 0` using `@Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hB) _ _`. Take `⟨c, hc⟩` from `(H1π_eq_zero_iff _).mp h0`. Take `⟨c', rfl⟩` from `Finsupp.mapRange_surjective f.hom.toLinearMap (map_zero _) hsurj' c`. Use `⟨y - d₂₁ A c', fun g => ?_, ?_⟩` and prove the remaining obligations.

Establish `h2 : L (d₂₁ A c') = L y` using `(d₂₁_mapRange f c').symm.trans hc`. Establish `h4 : L (y - d₂₁ A c') = 0`. Establish `h5 : L (y - d₂₁ A c') = L y - L (d₂₁ A c')` using `map_sub L y _`. Rewrite using `[h5, h2, sub_self]`. Use `congrArg (fun w => w g) h4` as an intermediate fact.

Simplify `this` using `[L]`. Establish `h3 : d₁₀ A (d₂₁ A c') = 0` using `by simp`. Establish `h5 : d₁₀ A (y - d₂₁ A c') = d₁₀ A y - d₁₀ A (d₂₁ A c')` using `map_sub (d₁₀ A).hom y _`. Rewrite using `[h5, h3, sub_zero]`. Conclude with `hy`.
-/
theorem exists_chain_ker_of_isZero_groupHomology_one (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1)) {x : A}
    (hx : f.hom x = 0) (hxI : x ∈ Coinvariants.ker A.ρ) :
    ∃ z : G →₀ A, (∀ g, f.hom (z g) = 0) ∧ d₁₀ A z = x := by
  have hsurj' : Function.Surjective f.hom.toLinearMap := hsurj
  obtain ⟨y, hy⟩ : x ∈ LinearMap.range (d₁₀ A).hom := by
    rw [range_d₁₀_eq_coinvariantsKer]
    exact hxI
  let L := Finsupp.mapRange.linearMap (α := G) f.hom.toLinearMap
  have hY : L y ∈ cycles₁ B := by
    change d₁₀ B (L y) = 0
    rw [d₁₀_mapRange f y]
    change f.hom (d₁₀ A y) = 0
    rw [show d₁₀ A y = x from hy]
    exact hx
  have h0 : H1π B ⟨L y, hY⟩ = 0 :=
    @Subsingleton.elim _ (ModuleCat.subsingleton_of_isZero hB) _ _
  obtain ⟨c, hc⟩ := (H1π_eq_zero_iff _).mp h0
  obtain ⟨c', rfl⟩ := Finsupp.mapRange_surjective f.hom.toLinearMap (map_zero _) hsurj' c
  refine ⟨y - d₂₁ A c', fun g => ?_, ?_⟩
  · have h2 : L (d₂₁ A c') = L y := (d₂₁_mapRange f c').symm.trans hc
    have h4 : L (y - d₂₁ A c') = 0 := by
      have h5 : L (y - d₂₁ A c') = L y - L (d₂₁ A c') := map_sub L y _
      rw [h5, h2, sub_self]
    have := congrArg (fun w => w g) h4
    simpa [L] using this
  · have h3 : d₁₀ A (d₂₁ A c') = 0 := by simp
    have h5 : d₁₀ A (y - d₂₁ A c') = d₁₀ A y - d₁₀ A (d₂₁ A c') := map_sub (d₁₀ A).hom y _
    rw [h5, h3, sub_zero]
    exact hy

end Chains

section PGroup

variable {k G : Type u} [Field k] [Group G] [Fintype G] {p : ℕ} [Fact p.Prime] [CharP k p]

/- English proof (translation)
Set `K` to `LinearMap.ker f.hom.toLinearMap`. Establish `hK : ∀ g, K ≤ K.comap (A.ρ g)` using `fun g x hx => by`. Establish `hx' : f.hom x = 0` using `LinearMap.mem_ker.mp hx`. Use `LinearMap.mem_ker.mpr ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `f.hom (A.ρ g x) = 0`.

Rewrite using `[Rep.hom_comm_apply, hx', map_zero]`. Set `ρK : @Representation k G K _ _ AddCommGroup.toAddCommMonoid _` to `A.ρ.subrepresentation K hK`. Establish `hKI : Coinvariants.ker (k` using `k) (G := G) (V := K) ρK = ⊤ := by`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨x, hx⟩ -`.

Establish `hx0 : f.hom x = 0` using `LinearMap.mem_ker.mp hx`. Take `⟨z, hz, hdz⟩` from `exists_chain_ker_of_isZero_groupHomology_one f hsurj hB hx0 (hker x hx0)`. Establish `hzK : ∀ g, z g ∈ K` using `fun g => LinearMap.mem_ker.mpr (hz g)`. Establish `hmem : (⟨x, hx⟩ : K) = ∑ g ∈ z.support, (ρK g⁻¹ ⟨z g, hzK g⟩ - ⟨z g, hzK g⟩)`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[Submodule.coe_sum]`. Express the relevant statement in the definitionally equal form `x = _`. Rewrite using `[← hdz, d₁₀_apply_eq_sum]`. Both sides reduce to the same expression. Rewrite using `[hmem]`.

Conclude with `Submodule.sum_mem _ fun g _ => Coinvariants.sub_mem_ker g⁻¹ _`. Establish `hKs : Subsingleton K`. Apply `subsingleton_of_coinvariantsKer_eq_top hG ρK` to reduce the goal to its premises. Conclude with `hKI`. Introduce `x y hxy`.

Establish `hxy' : x - y ∈ K` using `LinearMap.mem_ker.mpr (by`. Express the relevant statement in the definitionally equal form `f.hom (x - y) = 0`. Rewrite using `[map_sub, hxy, sub_self])`. Conclude with `sub_eq_zero.mp (congrArg Subtype.val (Subsingleton.elim (⟨x - y, hxy'⟩ : K) 0))`.
-/
theorem injective_of_isZero_groupHomology_one (hG : IsPGroup p G) {A B : Rep.{u} k G} (f : A ⟶ B)
    (hsurj : Function.Surjective f.hom) (hB : IsZero (groupHomology B 1))
    (hker : ∀ x, f.hom x = 0 → x ∈ Coinvariants.ker A.ρ) : Function.Injective f.hom := by
  let K := LinearMap.ker f.hom.toLinearMap
  have hK : ∀ g, K ≤ K.comap (A.ρ g) := fun g x hx => by
    have hx' : f.hom x = 0 := LinearMap.mem_ker.mp hx
    refine LinearMap.mem_ker.mpr ?_
    change f.hom (A.ρ g x) = 0
    rw [Rep.hom_comm_apply, hx', map_zero]
  let ρK : @Representation k G K _ _ AddCommGroup.toAddCommMonoid _ := A.ρ.subrepresentation K hK
  have hKI : Coinvariants.ker (k := k) (G := G) (V := K) ρK = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx0 : f.hom x = 0 := LinearMap.mem_ker.mp hx
    obtain ⟨z, hz, hdz⟩ := exists_chain_ker_of_isZero_groupHomology_one f hsurj hB hx0 (hker x hx0)
    have hzK : ∀ g, z g ∈ K := fun g => LinearMap.mem_ker.mpr (hz g)
    have hmem : (⟨x, hx⟩ : K) = ∑ g ∈ z.support, (ρK g⁻¹ ⟨z g, hzK g⟩ - ⟨z g, hzK g⟩) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change x = _
      rw [← hdz, d₁₀_apply_eq_sum]
      rfl
    rw [hmem]
    exact Submodule.sum_mem _ fun g _ => Coinvariants.sub_mem_ker g⁻¹ _
  have hKs : Subsingleton K := by
    apply subsingleton_of_coinvariantsKer_eq_top hG ρK
    exact hKI
  intro x y hxy
  have hxy' : x - y ∈ K := LinearMap.mem_ker.mpr (by
    change f.hom (x - y) = 0
    rw [map_sub, hxy, sub_self])
  exact sub_eq_zero.mp (congrArg Subtype.val (Subsingleton.elim (⟨x - y, hxy'⟩ : K) 0))

/- English proof (translation)
Set `ι` to `Module.Free.ChooseBasisIndex k (Coinvariants M.ρ)`. Set `b : Module.Basis ι k (Coinvariants M.ρ)` to `Module.Free.chooseBasis k (Coinvariants M.ρ)`. Use `choose e he using fun i => Coinvariants.mk_surjective M.ρ (b i)`. Set `π : Rep.free k G ι ⟶ M` to `Rep.freeLift (k := k) (G := G) (A := M) e`. Establish `hπ : ∀ i g r, π.hom (single i (MonoidAlgebra.single g r)) = r • M.ρ g (e i)` using `fun i g r => by simp [π]`.

Establish `hsurj : Function.Surjective π.hom`. Establish `hr : LinearMap.range π.hom.toLinearMap = ⊤`. Apply `eq_top_of_sup_coinvariantsKer_eq_top hG M.ρ` to reduce the goal to its premises. Introduce and unpack `g _ ⟨y, rfl⟩`. Conclude with `LinearMap.mem_range.mpr ⟨(Rep.free k G ι).ρ g y, Rep.hom_comm_apply π g y⟩`.

Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : Coinvariants.mk M.ρ x ∈ Submodule.span k (Set.range b)` using `b.span_eq ▸ Submodule.mem_top`. Establish `hmap : Submodule.span k (Set.range b) ≤ (LinearMap.range π.hom.toLinearMap).map (Coinvariants.mk M.ρ)`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.mem_map.mpr ⟨e i, LinearMap.mem_range.mpr ⟨single i (MonoidAlgebra.single 1 1), by simpa using hπ i 1 1⟩, he i⟩`. Take `⟨w, hw, hwx⟩` from `Submodule.mem_map.mp (hmap hx)`. Establish `hxw : x - w ∈ Coinvariants.ker M.ρ` using `(Coinvariants.mk_eq_iff M.ρ).mp hwx.symm`. Rewrite using `[show x = w + (x - w) by abel]`.

Conclude with `Submodule.add_mem_sup hw hxw`. Conclude with `LinearMap.range_eq_top.mp hr`. Set `lam : M.V →ₗ[k] (ι →₀ k)` to `b.repr.toLinearMap ∘ₗ Coinvariants.mk M.ρ`. Set `s : (ι →₀ k) →ₗ[k] (ι →₀ k[G])` to `Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle 1)`. Establish `hlam : ∀ y, y - s (lam (π.hom y)) ∈ Coinvariants.ker (Representation.free k G ι)`.

Introduce `y`. Proceed by induction on `y using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add y₁ y₂ h₁ h₂`. Rewrite using `[map_add, map_add, map_add, add_sub_add_comm]`.

Conclude with `add_mem h₁ h₂`. Consider the case `single i a`. Proceed by induction on `a using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp`. Consider the case `add a₁ a₂ h₁ h₂`.

Rewrite using `[Finsupp.single_add, map_add, map_add, map_add, add_sub_add_comm]`. Conclude with `add_mem h₁ h₂`. Consider the case `single g r`. Use `Coinvariants.mem_ker_of_eq g (single i (MonoidAlgebra.single 1 r)) _ ?_` and prove the remaining obligations. Rewrite using `[hπ]`.

Simplify using `[lam, s, he]`. Establish `hker : ∀ x, π.hom x = 0 → x ∈ Coinvariants.ker (Rep.free k G ι).ρ` using `fun x hx => by`. Simplify `hlam x` using `[hx]`. Establish `hinj : Function.Injective π.hom` using `injective_of_isZero_groupHomology_one hG π hsurj hM hker`. Set `eqv : (Representation.free k G ι).Equiv M.ρ` to `Representation.Equiv.mk (LinearEquiv.ofBijective π.hom.toLinearMap ⟨hinj, hsurj⟩) fun g => LinearMap.ext fun y => Rep.hom_comm_apply π g y`.

Conclude with `⟨ι, ⟨Rep.mkIso eqv⟩⟩`.
-/
theorem exists_iso_free_of_isZero_groupHomology_one (hG : IsPGroup p G) (M : Rep.{u} k G)
    (hM : IsZero (groupHomology M 1)) : ∃ ι : Type u, Nonempty (Rep.free k G ι ≅ M) := by
  classical

  let ι := Module.Free.ChooseBasisIndex k (Coinvariants M.ρ)
  let b : Module.Basis ι k (Coinvariants M.ρ) := Module.Free.chooseBasis k (Coinvariants M.ρ)
  choose e he using fun i => Coinvariants.mk_surjective M.ρ (b i)
  let π : Rep.free k G ι ⟶ M := Rep.freeLift (k := k) (G := G) (A := M) e
  have hπ : ∀ i g r, π.hom (single i (MonoidAlgebra.single g r)) = r • M.ρ g (e i) :=
    fun i g r => by simp [π]

  have hsurj : Function.Surjective π.hom := by
    have hr : LinearMap.range π.hom.toLinearMap = ⊤ := by
      apply eq_top_of_sup_coinvariantsKer_eq_top hG M.ρ
      · rintro g _ ⟨y, rfl⟩
        exact LinearMap.mem_range.mpr ⟨(Rep.free k G ι).ρ g y, Rep.hom_comm_apply π g y⟩
      · rw [eq_top_iff]
        intro x _
        have hx : Coinvariants.mk M.ρ x ∈ Submodule.span k (Set.range b) :=
          b.span_eq ▸ Submodule.mem_top
        have hmap : Submodule.span k (Set.range b) ≤
            (LinearMap.range π.hom.toLinearMap).map (Coinvariants.mk M.ρ) := by
          rw [Submodule.span_le]
          rintro _ ⟨i, rfl⟩
          exact Submodule.mem_map.mpr ⟨e i, LinearMap.mem_range.mpr
            ⟨single i (MonoidAlgebra.single 1 1), by simpa using hπ i 1 1⟩, he i⟩
        obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp (hmap hx)
        have hxw : x - w ∈ Coinvariants.ker M.ρ := (Coinvariants.mk_eq_iff M.ρ).mp hwx.symm
        rw [show x = w + (x - w) by abel]
        exact Submodule.add_mem_sup hw hxw
    exact LinearMap.range_eq_top.mp hr

  let lam : M.V →ₗ[k] (ι →₀ k) := b.repr.toLinearMap ∘ₗ Coinvariants.mk M.ρ
  let s : (ι →₀ k) →ₗ[k] (ι →₀ k[G]) := Finsupp.mapRange.linearMap (MonoidAlgebra.lsingle 1)
  have hlam : ∀ y, y - s (lam (π.hom y)) ∈ Coinvariants.ker (Representation.free k G ι) := by
    intro y
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      rw [map_add, map_add, map_add, add_sub_add_comm]
      exact add_mem h₁ h₂
    | single i a =>
      induction a using MonoidAlgebra.induction_linear with
      | zero => simp
      | add a₁ a₂ h₁ h₂ =>
        rw [Finsupp.single_add, map_add, map_add, map_add, add_sub_add_comm]
        exact add_mem h₁ h₂
      | single g r =>
        refine Coinvariants.mem_ker_of_eq g (single i (MonoidAlgebra.single 1 r)) _ ?_
        rw [hπ]
        simp [lam, s, he]
  have hker : ∀ x, π.hom x = 0 → x ∈ Coinvariants.ker (Rep.free k G ι).ρ := fun x hx => by
    simpa [hx] using hlam x

  have hinj : Function.Injective π.hom :=
    injective_of_isZero_groupHomology_one hG π hsurj hM hker
  let eqv : (Representation.free k G ι).Equiv M.ρ :=
    Representation.Equiv.mk (LinearEquiv.ofBijective π.hom.toLinearMap ⟨hinj, hsurj⟩) fun g =>
      LinearMap.ext fun y => Rep.hom_comm_apply π g y
  exact ⟨ι, ⟨Rep.mkIso eqv⟩⟩

/- English proof (translation)
Set `φ` to `Representation.equivOfIso e`. Use `Representation.free_asModule_free k G ι` as an intermediate fact. Conclude with `Module.Free.of_equiv (LinearEquiv.ofLinearMap (IntertwiningMap.equivLinearMapAsModule (ρ := (Rep.free k G ι).ρ) (σ := M.ρ) φ.toIntertwiningMap) (IntertwiningMap.equivLinearMapAsModule (ρ := M.ρ) (σ := (Rep.free k G ι).ρ) φ.symm.toIntertwiningMap) (LinearMap.ext fun x => φ.apply_s …`.
-/
theorem free_asModule_of_iso_free {k G : Type u} [CommRing k] [Group G] {M : Rep.{u} k G}
    {ι : Type u} (e : Rep.free k G ι ≅ M) : Module.Free k[G] M.ρ.asModule := by
  let φ := Representation.equivOfIso e
  have := Representation.free_asModule_free k G ι
  exact Module.Free.of_equiv (LinearEquiv.ofLinearMap
    (IntertwiningMap.equivLinearMapAsModule (ρ := (Rep.free k G ι).ρ) (σ := M.ρ) φ.toIntertwiningMap)
    (IntertwiningMap.equivLinearMapAsModule (ρ := M.ρ) (σ := (Rep.free k G ι).ρ)
      φ.symm.toIntertwiningMap)
    (LinearMap.ext fun x => φ.apply_symm_apply x) (LinearMap.ext fun x => φ.symm_apply_apply x))

end PGroup

end GroundTheory.GroupCoh

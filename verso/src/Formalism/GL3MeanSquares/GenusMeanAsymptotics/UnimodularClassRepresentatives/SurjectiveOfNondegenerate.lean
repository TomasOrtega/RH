import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsDualBound
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsLatticeOfFibLocNeZeroGood

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.D2.IA

/- English proof (translation)
Unfold `Subgroup.relIndex AddSubgroup.relIndex Subgroup.index AddSubgroup.index`. Set `g : (T ⧸ H.subgroupOf T) → (N ⧸ N'.addSubgroupOf N)` to `Quotient.lift (s := QuotientGroup.leftRel (H.subgroupOf T)) (fun X : T => ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N)) (by`. Introduce `X Y hXY`. Establish `hXY` using `QuotientGroup.leftRel_apply.1 hXY`. Establish `h1 : f X - f Y ∈ N'` using `(hc X X.2 Y Y.2).1 (by simpa [Subgroup.mem_subgroupOf] using hXY)`.

Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Use `N'.neg_mem h1` as an intermediate fact. Simplify `this)` using `[neg_add_eq_sub]`. Use `Nat.card_eq_of_bijective g ⟨?_, ?_⟩` and prove the remaining obligations. Introduce `a b`.

Proceed by induction on `a using QuotientGroup.induction_on with | _ X => ?_`. Proceed by induction on `b using QuotientGroup.induction_on with | _ Y => ?_`. Introduce `hab`. Establish `h1 : ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N) = ((⟨f Y, hf Y Y.2⟩ : N) : N ⧸ N'.addSubgroupOf N)` using `hab`. Rewrite `h1` using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`.

Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Establish `h2 : f X - f Y ∈ N'`. Use `N'.neg_mem h1` as an intermediate fact. Simplify `this` using `[neg_add_eq_sub]`. Simplify using `using (hc X X.2 Y Y.2).2 h2`.

Introduce `b`. Proceed by induction on `b using QuotientAddGroup.induction_on with | _ Z => ?_`. Take `⟨X, hX, hXZ⟩` from `hsurj Z Z.2`. Use `⟨((⟨X, hX⟩ : T) : T ⧸ H.subgroupOf T), ?_⟩` and prove the remaining obligations. Use `show ((⟨f X, hf X hX⟩ : N) : N ⧸ N'.addSubgroupOf N) = (Z : N ⧸ N'.addSubgroupOf N)`.

Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`. Use `N'.neg_mem hXZ` as an intermediate fact. Simplify `this` using `[neg_add_eq_sub]`.
-/
theorem relIndex_eq_of_map {G M : Type*} [Group G] [AddCommGroup M] (H T : Subgroup G)
    (N' N : AddSubgroup M) (f : G → M) (hf : ∀ X ∈ T, f X ∈ N)
    (hc : ∀ X ∈ T, ∀ Y ∈ T, X⁻¹ * Y ∈ H ↔ f X - f Y ∈ N')
    (hsurj : ∀ Z ∈ N, ∃ X ∈ T, f X - Z ∈ N') : H.relIndex T = N'.relIndex N := by
  unfold Subgroup.relIndex AddSubgroup.relIndex Subgroup.index AddSubgroup.index
  let g : (T ⧸ H.subgroupOf T) → (N ⧸ N'.addSubgroupOf N) :=
    Quotient.lift (s := QuotientGroup.leftRel (H.subgroupOf T))
      (fun X : T => ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N)) (by
        intro X Y hXY
        have hXY := QuotientGroup.leftRel_apply.1 hXY
        have h1 : f X - f Y ∈ N' := (hc X X.2 Y Y.2).1 (by simpa [Subgroup.mem_subgroupOf] using hXY)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        have := N'.neg_mem h1
        simpa [neg_add_eq_sub] using this)
  refine Nat.card_eq_of_bijective g ⟨?_, ?_⟩
  · intro a b
    induction a using QuotientGroup.induction_on with | _ X => ?_
    induction b using QuotientGroup.induction_on with | _ Y => ?_
    intro hab
    have h1 : ((⟨f X, hf X X.2⟩ : N) : N ⧸ N'.addSubgroupOf N) = ((⟨f Y, hf Y Y.2⟩ : N) : N ⧸ N'.addSubgroupOf N) := hab
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h2 : f X - f Y ∈ N' := by
      have := N'.neg_mem h1
      simpa [neg_add_eq_sub] using this
    simpa using (hc X X.2 Y Y.2).2 h2
  · intro b
    induction b using QuotientAddGroup.induction_on with | _ Z => ?_
    obtain ⟨X, hX, hXZ⟩ := hsurj Z Z.2
    refine ⟨((⟨X, hX⟩ : T) : T ⧸ H.subgroupOf T), ?_⟩
    show ((⟨f X, hf X hX⟩ : N) : N ⧸ N'.addSubgroupOf N) = (Z : N ⧸ N'.addSubgroupOf N)
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    have := N'.neg_mem hXZ
    simpa [neg_add_eq_sub] using this

variable {K : Type} [Field K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/- English proof (translation)
Establish `hinj : Function.Injective h`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Conclude with `hn.1 x (fun y => by rw [hx]; rfl)`. Establish `hbij : Function.Bijective (h.rangeRestrict)` using `⟨fun a b hab => hinj (congrArg Subtype.val hab), h.surjective_rangeRestrict⟩`.

Set `j : V ≃+ LinearMap.range h` to `AddEquiv.ofBijective (h.rangeRestrict).toAddMonoidHom hbij`. Establish `hr : Module.rank K V = Module.rank K (LinearMap.range h)` using `rank_eq_of_equiv_equiv (starRingEnd K) j star_involutive.bijective (fun r m => by`. Apply `Subtype.ext` to reduce the goal to its premises. Use `show h (r • m) = (starRingEnd K) r • h m`. Rewrite using `[map_smulₛₗ])`.

Establish `hf : finrank K (LinearMap.range h) = finrank K (Dual K V)`. Rewrite using `[Subspace.dual_finrank_eq]`. Unfold `finrank`. Rewrite using `[hr]`. Establish `htop` using `Submodule.eq_top_of_finrank_eq hf`.

Conclude with `LinearMap.range_eq_top.1 htop`.
-/
theorem surjective_of_nondegenerate {h : V →ₗ⋆[K] V →ₗ[K] K} (hn : h.Nondegenerate) :
    Function.Surjective h := by
  have hinj : Function.Injective h := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact hn.1 x (fun y => by rw [hx]; rfl)
  have hbij : Function.Bijective (h.rangeRestrict) :=
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), h.surjective_rangeRestrict⟩
  let j : V ≃+ LinearMap.range h := AddEquiv.ofBijective (h.rangeRestrict).toAddMonoidHom hbij
  have hr : Module.rank K V = Module.rank K (LinearMap.range h) :=
    rank_eq_of_equiv_equiv (starRingEnd K) j star_involutive.bijective (fun r m => by
      apply Subtype.ext
      show h (r • m) = (starRingEnd K) r • h m
      rw [map_smulₛₗ])
  have hf : finrank K (LinearMap.range h) = finrank K (Dual K V) := by
    rw [Subspace.dual_finrank_eq]
    unfold finrank
    rw [hr]
  have htop := Submodule.eq_top_of_finrank_eq hf
  exact LinearMap.range_eq_top.1 htop

/- English proof (translation)
Establish `hex : ∀ y, ∃ w, ∀ x, h x w = s x y`. Introduce `y`. Set `l : V →ₗ[K] K` to `{ toFun := fun x => star (s x y) map_add' := fun a b => by simp map_smul' := fun a b => by simp [starRingEnd_apply] }`. Take `⟨w, hw⟩` from `surjective_of_nondegenerate hn l`. Use `⟨w, fun x => ?_⟩` and prove the remaining obligations.

Establish `h1 : h w x = star (s x y)` using `by rw [hw]; rfl`. Establish `h2` using `hs.eq w x`. Rewrite using `[← h2, h1, starRingEnd_apply, star_star]`. Use `choose Y hY using hex`. Use `⟨{ toFun := Y, map_add' := fun a b => ?_, map_smul' := fun a b => ?_ }, fun x y => hY y x⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero]`. Use `hn.2 _ (fun x => ?_)` and prove the remaining obligations. Rewrite using `[map_sub, map_add, hY, hY, hY, map_add, sub_self]`. Rewrite using `[← sub_eq_zero]`. Use `hn.2 _ (fun x => ?_)` and prove the remaining obligations.

Rewrite using `[RingHom.id_apply, map_sub, map_smul, hY, hY, map_smul, sub_self]`.
-/
theorem exists_adj {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hn : h.Nondegenerate)
    (s : V →ₗ⋆[K] V →ₗ[K] K) : ∃ Y : V →ₗ[K] V, ∀ x y, h x (Y y) = s x y := by
  have hex : ∀ y, ∃ w, ∀ x, h x w = s x y := by
    intro y
    let l : V →ₗ[K] K :=
      { toFun := fun x => star (s x y)
        map_add' := fun a b => by simp
        map_smul' := fun a b => by simp [starRingEnd_apply] }
    obtain ⟨w, hw⟩ := surjective_of_nondegenerate hn l
    refine ⟨w, fun x => ?_⟩
    have h1 : h w x = star (s x y) := by rw [hw]; rfl
    have h2 := hs.eq w x
    rw [← h2, h1, starRingEnd_apply, star_star]
  choose Y hY using hex
  refine ⟨{ toFun := Y, map_add' := fun a b => ?_, map_smul' := fun a b => ?_ }, fun x y => hY y x⟩
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [map_sub, map_add, hY, hY, hY, map_add, sub_self]
  · rw [← sub_eq_zero]
    refine hn.2 _ (fun x => ?_)
    rw [RingHom.id_apply, map_sub, map_smul, hY, hY, map_smul, sub_self]

section Lat

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

def phi (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) : V →ₗ⋆[K] V →ₗ[K] K :=
  (h.comp (X : V →ₗ[K] V)).compl₂ (X : V →ₗ[K] V) - h

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem phi_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : V ≃ₗ[K] V) (x y : V) :
    phi h X x y = h (X x) (X y) - h x y := rfl

/- English proof (translation)
Establish `e : ∀ a b, star (h a b) = h b a` using `fun a b => hs.eq a b`. Rewrite using `[phi_apply, phi_apply, star_sub, e, e]`.
-/
theorem star_phi {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : V ≃ₗ[K] V) (x y : V) :
    star (phi h X x y) = phi h X y x := by
  have e : ∀ a b, star (h a b) = h b a := fun a b => hs.eq a b
  rw [phi_apply, phi_apply, star_sub, e, e]

/- English proof (translation)
Introduce `h0`. Establish `h1 : (π : F) = 0` using `(map_eq_zero (algebraMap F K)).1 h0`. Establish `h2 : π = 0` using `by exact_mod_cast h1`. Conclude with `hπ' (h2 ▸ zero_mem _)`.
-/
theorem unif_ne_zero {𝔭 : Ideal (𝓞 F)} {π : 𝓞 F} (hπ' : π ∉ 𝔭 ^ 2) : algebraMap F K (π : F) ≠ 0 := by
  intro h0
  have h1 : (π : F) = 0 := (map_eq_zero (algebraMap F K)).1 h0
  have h2 : π = 0 := by exact_mod_cast h1
  exact hπ' (h2 ▸ zero_mem _)

/- English proof (translation)
Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`. Establish `h0 : algebraMap F K (π : F) ≠ 0` using `unif_ne_zero hπ'`. Establish `hst : star (algebraMap F K (π : F)) = algebraMap F K (π : F)` using `(hF _).2 ⟨_, rfl⟩`. Introduce `x hx y hy`. Establish `hx' : algebraMap F K (π : F) ^ r • x ∈ locF 𝔭 B₀` using `hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨x, hx, rfl⟩)`.

Establish `hy' : algebraMap F K (π : F) ^ r • y ∈ locF 𝔭 B₀` using `hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨y, hy, rfl⟩)`. Establish `h1` using `pK_anti (K := K) 𝔭 hnm (hs _ hx' _ hy')`. Rewrite `h1` using `[map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_pow, hst, smul_eq_mul, smul_eq_mul]`. Take `⟨b, hb, e⟩` from `(mem_pK_iff_unif h𝔭 hπ hπ').1 h1`. Use `(mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, ?_⟩` and prove the remaining obligations.

Apply `mul_left_cancel₀ (pow_ne_zero (2 * r) h0)` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation.
-/
theorem sesq_scale (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (s : V →ₗ⋆[K] V →ₗ[K] K) {n m : ℕ} (hnm : n + 2 * r ≤ m)
    (hs : ∀ x ∈ locF 𝔭 B₀, ∀ y ∈ locF 𝔭 B₀, s x y ∈ pK K 𝔭 m) :
    ∀ x ∈ locF 𝔭 A₀, ∀ y ∈ locF 𝔭 A₀, s x y ∈ pK K 𝔭 n := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  have hst : star (algebraMap F K (π : F)) = algebraMap F K (π : F) := (hF _).2 ⟨_, rfl⟩
  intro x hx y hy
  have hx' : algebraMap F K (π : F) ^ r • x ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨x, hx, rfl⟩)
  have hy' : algebraMap F K (π : F) ^ r • y ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨y, hy, rfl⟩)
  have h1 := pK_anti (K := K) 𝔭 hnm (hs _ hx' _ hy')
  rw [map_smul, map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_pow, hst, smul_eq_mul, smul_eq_mul] at h1
  obtain ⟨b, hb, e⟩ := (mem_pK_iff_unif h𝔭 hπ hπ').1 h1
  refine (mem_pK_iff_unif h𝔭 hπ hπ').2 ⟨b, hb, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (2 * r) h0)
  calc algebraMap F K (π : F) ^ (2 * r) * s x y
      = algebraMap F K (π : F) ^ r * (algebraMap F K (π : F) ^ r * s x y) := by ring
    _ = algebraMap F K (π : F) ^ (n + 2 * r) * b := e
    _ = _ := by ring

/- English proof (translation)
Take `⟨π, hπ, hπ'⟩` from `exists_unif h𝔭`. Establish `h0 : algebraMap F K (π : F) ≠ 0` using `unif_ne_zero hπ'`. Introduce `x hx`. Establish `hx' : algebraMap F K (π : F) ^ r' • x ∈ locF 𝔭 A₀` using `hr' ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)`. Establish `h1` using `smul_anti 𝔭 (locF 𝔭 A₀) hnm (hY _ hx')`.

Take `⟨a, ha, e⟩` from `(mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h1`. Establish `ha' : algebraMap F K (π : F) ^ r • a ∈ locF 𝔭 B₀` using `hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨a, ha, rfl⟩)`. Use `(mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, ha', ?_⟩` and prove the remaining obligations. Rewrite `e` using `[map_smul]`. Apply `smul_right_injective V (pow_ne_zero r' h0)` to reduce the goal to its premises.

Use `show algebraMap F K (π : F) ^ r' • Y x = algebraMap F K (π : F) ^ r' • _`. Rewrite using `[e, smul_smul, smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem end_scale {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {A₀ B₀ : Submodule (𝓞 K) V} {r r' : ℕ}
    (hr : extP K 𝔭 ^ r • locF 𝔭 A₀ ≤ locF 𝔭 B₀) (hr' : extP K 𝔭 ^ r' • locF 𝔭 B₀ ≤ locF 𝔭 A₀)
    (Y : V →ₗ[K] V) {n m : ℕ} (hnm : n + r + r' ≤ m)
    (hY : ∀ x ∈ locF 𝔭 A₀, Y x ∈ extP K 𝔭 ^ m • locF 𝔭 A₀) :
    ∀ x ∈ locF 𝔭 B₀, Y x ∈ extP K 𝔭 ^ n • locF 𝔭 B₀ := by
  obtain ⟨π, hπ, hπ'⟩ := exists_unif h𝔭
  have h0 : algebraMap F K (π : F) ≠ 0 := unif_ne_zero hπ'
  intro x hx
  have hx' : algebraMap F K (π : F) ^ r' • x ∈ locF 𝔭 A₀ :=
    hr' ((mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨x, hx, rfl⟩)
  have h1 := smul_anti 𝔭 (locF 𝔭 A₀) hnm (hY _ hx')
  obtain ⟨a, ha, e⟩ := (mem_smul_iff_unif h𝔭 hπ hπ' A₀).1 h1
  have ha' : algebraMap F K (π : F) ^ r • a ∈ locF 𝔭 B₀ :=
    hr ((mem_smul_iff_unif h𝔭 hπ hπ' A₀).2 ⟨a, ha, rfl⟩)
  refine (mem_smul_iff_unif h𝔭 hπ hπ' B₀).2 ⟨_, ha', ?_⟩
  rw [map_smul] at e
  apply smul_right_injective V (pow_ne_zero r' h0)
  show algebraMap F K (π : F) ^ r' • Y x = algebraMap F K (π : F) ^ r' • _
  rw [e, smul_smul, smul_smul]
  congr 1
  ring

end Lat

end Formalism.HermitianLattices.Ext.L3.D2.IA

import Development.EtaleCohomology.KummerTheory.LimitPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.KummerTheory

def LimRatBij : Prop := ∀ (l : ℕ) [Fact l.Prime] (P Q : Type 1) [AddCommGroup P] [Module ℤ_[l] P] [AddCommGroup Q]
  [Module ℤ_[l] Q] (f : P →ₗ[ℤ_[l]] Q) (N : ℕ), 0 < N → IsoUpTo N f → Function.Bijective (f.baseChange ℚ_[l])

def LimRatAssemble : Prop := A9 → ∀ (l : ℕ) [Fact l.Prime] {X Y S : Scheme.{0}} (pX : X ⟶ S) (pY : Y ⟶ S) (n i : ℤ) (M : ℕ)
  (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Hl l (sch.obj X) a i), n ≤ M → (∀ a ≤ M, QBasis l (c a)) →
  ∀ (e : ∀ a : ℤ, Hl l (sch.obj X) a i →ₗ[ℤ_[l]] Hl l (sch.obj Y) (n - a) 0 →ₗ[ℤ_[l]] Hl l (sch.obj (pullback pX pY)) n i)
    (Φ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]]
      Hl l (sch.obj (pullback pX pY)) n i),
  (∀ y, Φ y = ∑ a : Fin (M + 1), ∑ s : Fin (r a), e ((a : ℕ) : ℤ) (c a s) (y a s)) →
  Function.Bijective (Φ.baseChange ℚ_[l]) →
  ∃ κ : (⨁ a : ℤ, HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) ≃ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i,
    ∀ (a : ℤ) (x : Hl l (sch.obj X) a i) (y : Hl l (sch.obj Y) (n - a) 0),
      κ (DirectSum.lof ℚ_[l] ℤ (fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0) a
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y

/- English proof (translation)
Introduce `hA9 l _ X Y S pX pY n i M N r c hnM hN hB e Φ hΦ hiso`. Conclude with `h2 hA9 l pX pY n i M r c hnM hB e Φ hΦ (h1 l _ _ Φ N hN hiso)`.
-/
theorem limAssembleCut (h1 : LimRatBij) (h2 : LimRatAssemble) : LimAssemble := by
  intro hA9 l _ X Y S pX pY n i M N r c hnM hN hB e Φ hΦ hiso
  exact h2 hA9 l pX pY n i M r c hnM hB e Φ hΦ (h1 l _ _ Φ N hN hiso)

/- English proof (translation)
Introduce `l _ P Q _ _ _ _ f N hN hiso`. Establish `hPl : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] P 1)` using `(isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange _ _ _)`. Establish `hQl : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1)` using `(isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange _ _ _)`. Establish `hNS : ((N : ℤ_[l])) ∈ nonZeroDivisors ℤ_[l]` using `mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hN.ne')`. Establish `hne : ∀ s ∈ nonZeroDivisors ℤ_[l], algebraMap ℤ_[l] ℚ_[l] s ≠ 0` using `fun s hs => IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs`.

Establish `hsm : ∀ {V : Type 1} [AddCommGroup V] [Module ℤ_[l] V] (s : nonZeroDivisors ℤ_[l]) (w : ℚ_[l] ⊗[ℤ_[l]] V), s • w = algebraMap ℤ_[l] ℚ_[l] s • w` using `fun s w => by`. Rewrite using `[Submonoid.smul_def, algebraMap_smul]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`.

Take `⟨⟨x, s⟩, hs⟩` from `IsLocalizedModule.surj (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) w`. Simplify using `only [TensorProduct.mk_apply] at hs`. Establish `h1 : (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) (f x) = 0`. Rewrite using `[TensorProduct.mk_apply, ← LinearMap.baseChange_tmul, ← hs, hsm, map_smul, hw, smul_zero]`. Take `⟨t, ht⟩` from `(IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) _).mp h1`.

Establish `h2 : N • ((t : ℤ_[l]) • x) = 0` using `hiso.1 _ (by rw [map_smul]; exact ht)`. Establish `h3 : (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) x = 0`. Use `(IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) _).mpr ⟨⟨(N : ℤ_[l]) * t, Submonoid.mul_mem _ hNS t.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Submonoid.mk_smul, mul_smul, Nat.cast_smul_eq_nsmul]`. Conclude with `h2`.

Rewrite `h3` using `[TensorProduct.mk_apply]`. Rewrite `hs` using `[h3, hsm]`. Conclude with `(smul_eq_zero.mp hs).resolve_left (hne _ s.2)`. Introduce `w`. Take `⟨⟨z, s⟩, hs⟩` from `IsLocalizedModule.surj (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) w`.

Simplify using `only [TensorProduct.mk_apply] at hs`. Take `⟨x, hx⟩` from `hiso.2 z`. Establish `hc` using `hne _ (Submonoid.mul_mem _ hNS s.2)`. Use `⟨(algebraMap ℤ_[l] ℚ_[l] ((N : ℤ_[l]) * s))⁻¹ • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x), ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, LinearMap.baseChange_tmul, hx, ← Nat.cast_smul_eq_nsmul ℤ_[l], TensorProduct.tmul_smul, ← hs, Submonoid.smul_def, ← mul_smul, ← algebraMap_smul ℚ_[l] ((N : ℤ_[l]) * s) w]`.

Conclude with `inv_smul_smul₀ hc w`.
-/
theorem limRatBij : LimRatBij := by
  intro l _ P Q _ _ _ _ f N hN hiso
  have hPl : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange _ _ _)
  have hQl : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ_[l]) ℚ_[l] _).mpr (TensorProduct.isBaseChange _ _ _)
  have hNS : ((N : ℤ_[l])) ∈ nonZeroDivisors ℤ_[l] :=
    mem_nonZeroDivisors_of_ne_zero (Nat.cast_ne_zero.mpr hN.ne')
  have hne : ∀ s ∈ nonZeroDivisors ℤ_[l], algebraMap ℤ_[l] ℚ_[l] s ≠ 0 := fun s hs =>
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hsm : ∀ {V : Type 1} [AddCommGroup V] [Module ℤ_[l] V] (s : nonZeroDivisors ℤ_[l]) (w : ℚ_[l] ⊗[ℤ_[l]] V),
      s • w = algebraMap ℤ_[l] ℚ_[l] s • w := fun s w => by
    rw [Submonoid.smul_def, algebraMap_smul]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro w hw
    obtain ⟨⟨x, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) w
    simp only [TensorProduct.mk_apply] at hs
    have h1 : (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) (f x) = 0 := by
      rw [TensorProduct.mk_apply, ← LinearMap.baseChange_tmul, ← hs, hsm, map_smul, hw, smul_zero]
    obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) _).mp h1
    have h2 : N • ((t : ℤ_[l]) • x) = 0 := hiso.1 _ (by rw [map_smul]; exact ht)
    have h3 : (TensorProduct.mk ℤ_[l] ℚ_[l] P 1) x = 0 := by
      refine (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) _).mpr
        ⟨⟨(N : ℤ_[l]) * t, Submonoid.mul_mem _ hNS t.2⟩, ?_⟩
      rw [Submonoid.mk_smul, mul_smul, Nat.cast_smul_eq_nsmul]; exact h2
    rw [TensorProduct.mk_apply] at h3
    rw [h3, hsm] at hs
    exact (smul_eq_zero.mp hs).resolve_left (hne _ s.2)
  · intro w
    obtain ⟨⟨z, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] Q 1) w
    simp only [TensorProduct.mk_apply] at hs
    obtain ⟨x, hx⟩ := hiso.2 z
    have hc := hne _ (Submonoid.mul_mem _ hNS s.2)
    refine ⟨(algebraMap ℤ_[l] ℚ_[l] ((N : ℤ_[l]) * s))⁻¹ • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x), ?_⟩
    rw [map_smul, LinearMap.baseChange_tmul, hx, ← Nat.cast_smul_eq_nsmul ℤ_[l], TensorProduct.tmul_smul, ← hs,
      Submonoid.smul_def, ← mul_smul, ← algebraMap_smul ℚ_[l] ((N : ℤ_[l]) * s) w]
    exact inv_smul_smul₀ hc w

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `x y`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `k`. Conclude with `((hA9 (ZMod (l ^ k)) (tw (l ^ k) j)).1 E m hm).elim _ _`.
-/
theorem hl_sub (hA9 : A9) (l : ℕ) [Fact l.Prime] (E : Spc) (m j : ℤ) (hm : m < 0) : Subsingleton (Hl l E m j) := by
  constructor
  intro x y
  apply Subtype.ext
  funext k
  exact ((hA9 (ZMod (l ^ k)) (tw (l ^ k) j)).1 E m hm).elim _ _

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `hA9 l _ X Y S pX pY n i M r c hnM hB e Φ hΦ hbij`. Set `T` to `fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0`. Set `g : ∀ a : ℤ, T a →ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i` to `fun a => (TensorProduct.lift (e a)).baseChange ℚ_[l] ∘ₗ (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ_[l] ℚ_[l] _ _).symm.toLinearMap`. Establish `hg : ∀ a x y, g a (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y)) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y`. Introduce `a x y`.

Simplify using `only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]`. Use `erw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]`. Rewrite using `[LinearMap.baseChange_tmul, TensorProduct.lift.tmul, mul_one]`. Set `κ₀` to `DirectSum.toModule ℚ_[l] ℤ _ g`. Establish `hκ₀ : ∀ a x y, κ₀ (DirectSum.lof ℚ_[l] ℤ T a (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y`.

Introduce `a x y`. Simplify using `only [κ₀, DirectSum.toModule_lof]`. Conclude with `hg a x y`. Establish `hsm : ∀ (a : ℤ) (t : ℤ_[l]) (y : Hl l (sch.obj Y) (n - a) 0) (u : HQ l (sch.obj X) a i), u ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (t • y)) = algebraMap ℤ_[l] ℚ_[l] t • (u ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))`. Introduce `a t y u`.

Rewrite using `[← TensorProduct.tmul_smul, TensorProduct.tmul_smul (R := ℤ_[l]), algebraMap_smul]`. Set `ψ₀ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]] ⨁ a : ℤ, T a` to `{ toFun := fun y => ∑ a : Fin (M + 1), ∑ s : Fin (r a), DirectSum.lof ℚ_[l] ℤ T ((a : ℕ) : ℤ) (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c a s) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y a s)) map_add' := fun y z => by`. Simplify using `only [Pi.add_apply, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]`. Use the proof step `map_smul' := fun t y => by`. Simplify using `only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[hsm, map_smul, algebraMap_smul] }`. Set `ψ` to `ψ₀.liftBaseChange ℚ_[l]`. Establish `key : ∀ u, κ₀ (ψ u) = Φ.baseChange ℚ_[l] u`. Introduce `u`.

Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `add u v hu hv => rw [map_add, map_add, hu, hv, map_add]`. Consider the case `tmul q y`. Rewrite using `[LinearMap.liftBaseChange_tmul, map_smul, LinearMap.baseChange_tmul]`.

Express the relevant statement in the definitionally equal form `q • κ₀ (∑ a : Fin (M + 1), ∑ s : Fin (r a), _) = _`. Rewrite using `[hΦ y, TensorProduct.tmul_sum]`. Simplify using `only [map_sum, hκ₀, TensorProduct.tmul_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul, mul_one]`.

Establish `hsurj : Function.Surjective ψ`. Introduce `d`. It suffices to establish `h : d ∈ LinearMap.range ψ from h`. Proceed by induction on `d using DirectSum.induction_on with`. Consider the case `zero => exact Submodule.zero_mem _`.

Consider the case `add u v hu hv => exact Submodule.add_mem _ hu hv`. Consider the case `of a t`. Express the relevant statement in the definitionally equal form `DirectSum.lof ℚ_[l] ℤ T a t ∈ _`. Distinguish the cases in `ha0 : a < 0`. Use `haveI := hl_sub hA9 l (sch.obj X) a i ha0`.

Establish `: t = 0`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `add u v hu hv => rw [hu, hv, add_zero]`. Consider the case `tmul u v`.

Establish `: u = 0`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `add u v hu hv => rw [hu, hv, add_zero]`. Consider the case `tmul q x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]`.

Rewrite using `[this, TensorProduct.zero_tmul]`. Rewrite using `[this, map_zero]`. Conclude with `Submodule.zero_mem _`. Distinguish the cases in `haM : (M : ℤ) < a`. Use `haveI := hl_sub hA9 l (sch.obj Y) (n - a) 0 (by omega)`.

Establish `: t = 0`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `add u v hu hv => rw [hu, hv, add_zero]`. Consider the case `tmul u v`.

Establish `: v = 0`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `add u v hu hv => rw [hu, hv, add_zero]`. Consider the case `tmul q x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]`.

Rewrite using `[this, TensorProduct.tmul_zero]`. Rewrite using `[this, map_zero]`. Conclude with `Submodule.zero_mem _`. Take `⟨m, rfl⟩` from `Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ a)`. Establish `hm : m < M + 1` using `by omega`.

Establish `hbase : ∀ (s : Fin (r m)) (q : ℚ_[l]) (y : Hl l (sch.obj Y) (n - (m : ℤ)) 0), DirectSum.lof ℚ_[l] ℤ T (m : ℤ) (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c m s) ⊗ₜ[ℚ_[l]] (q ⊗ₜ[ℤ_[l]] y)) ∈ LinearMap.range ψ`. Introduce `s q y`. Use `⟨q ⊗ₜ[ℤ_[l]] (Pi.single (M := fun a : Fin (M + 1) => Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) ⟨m, hm⟩ (Pi.single s y)), ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.liftBaseChange_tmul]`. Express the relevant statement in the definitionally equal form `q • (∑ a : Fin (M + 1), ∑ s : Fin (r a), _) = _`.

Rewrite using `[Finset.sum_eq_single (⟨m, hm⟩ : Fin (M + 1))]`. Rewrite using `[Finset.sum_eq_single s]`. Simplify using `only [Pi.single_eq_same]`. Rewrite using `[← map_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Introduce `s' _ hs'`.

Rewrite using `[Pi.single_eq_same, Pi.single_eq_of_ne hs', TensorProduct.tmul_zero, TensorProduct.tmul_zero, map_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ s) h`. Introduce `b _ hb`. Rewrite using `[Pi.single_eq_of_ne hb]`.

Simplify using `only [Pi.zero_apply, TensorProduct.tmul_zero, map_zero, Finset.sum_const_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`. Establish `hspan` using `(hB m (by omega)).2`. It suffices to establish `goal : ∀ t' : HQ l (sch.obj X) (m : ℤ) i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - (m : ℤ)) 0, DirectSum.lof ℚ_[l] ℤ T (m : ℤ) t' ∈ LinearMap.range ψ from goal t`.

Introduce `t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add u v hu hv => rw [map_add]`.

Conclude with `Submodule.add_mem _ hu hv`. Consider the case `tmul u v`. Establish `hu : u ∈ Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c m s : HQ l (sch.obj X) (m : ℤ) i))`. Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`.

Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem u hu`. Take `⟨s, rfl⟩` from `hu`. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => rw [TensorProduct.tmul_zero, map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add v w hv hw => rw [TensorProduct.tmul_add, map_add]`. Conclude with `Submodule.add_mem _ hv hw`. Consider the case `tmul q y => exact hbase s q y`. Consider the case `zero => rw [TensorProduct.zero_tmul, map_zero]`.

Conclude with `Submodule.zero_mem _`. Consider the case `add u w _ _ hu hw => rw [TensorProduct.add_tmul, map_add]`. Conclude with `Submodule.add_mem _ hu hw`. Consider the case `smul k u _ hu => rw [← TensorProduct.smul_tmul', map_smul]`. Conclude with `Submodule.smul_mem _ k hu`.

Establish `hbijκ : Function.Bijective κ₀`. Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `d hd`. Take `⟨u, rfl⟩` from `hsurj d`.

Rewrite `hd` using `[key]`. Establish `: u = 0` using `(injective_iff_map_eq_zero _).mp hbij.1 u hd`. Rewrite using `[this, map_zero]`. Introduce `w`. Take `⟨u, rfl⟩` from `hbij.2 w`.

Conclude with `⟨ψ u, key u⟩`. Conclude with `⟨LinearEquiv.ofBijective κ₀ hbijκ, fun a x y => hκ₀ a x y⟩`.
-/
theorem limRatAssemble : LimRatAssemble := by
  intro hA9 l _ X Y S pX pY n i M r c hnM hB e Φ hΦ hbij
  let T := fun a : ℤ => HQ l (sch.obj X) a i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - a) 0
  let g : ∀ a : ℤ, T a →ₗ[ℚ_[l]] HQ l (sch.obj (pullback pX pY)) n i := fun a =>
    (TensorProduct.lift (e a)).baseChange ℚ_[l] ∘ₗ
      (TensorProduct.AlgebraTensorModule.distribBaseChange ℤ_[l] ℚ_[l] _ _).symm.toLinearMap
  have hg : ∀ a x y, g a (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y)) =
      (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y := by
    intro a x y
    simp only [g, LinearMap.comp_apply, LinearEquiv.coe_coe]
    erw [TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]
    rw [LinearMap.baseChange_tmul, TensorProduct.lift.tmul, mul_one]
  let κ₀ := DirectSum.toModule ℚ_[l] ℤ _ g
  have hκ₀ : ∀ a x y, κ₀ (DirectSum.lof ℚ_[l] ℤ T a
      (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y))) = (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] e a x y := by
    intro a x y
    simp only [κ₀, DirectSum.toModule_lof]
    exact hg a x y
  have hsm : ∀ (a : ℤ) (t : ℤ_[l]) (y : Hl l (sch.obj Y) (n - a) 0) (u : HQ l (sch.obj X) a i),
      u ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] (t • y)) = algebraMap ℤ_[l] ℚ_[l] t • (u ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y)) := by
    intro a t y u
    rw [← TensorProduct.tmul_smul, TensorProduct.tmul_smul (R := ℤ_[l]), algebraMap_smul]
  let ψ₀ : (∀ a : Fin (M + 1), Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0) →ₗ[ℤ_[l]] ⨁ a : ℤ, T a :=
    { toFun := fun y => ∑ a : Fin (M + 1), ∑ s : Fin (r a), DirectSum.lof ℚ_[l] ℤ T ((a : ℕ) : ℤ)
        (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c a s) ⊗ₜ[ℚ_[l]] ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y a s))
      map_add' := fun y z => by
        simp only [Pi.add_apply, TensorProduct.tmul_add, map_add, Finset.sum_add_distrib]
      map_smul' := fun t y => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
        rw [hsm, map_smul, algebraMap_smul] }
  let ψ := ψ₀.liftBaseChange ℚ_[l]
  have key : ∀ u, κ₀ (ψ u) = Φ.baseChange ℚ_[l] u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add u v hu hv => rw [map_add, map_add, hu, hv, map_add]
    | tmul q y =>
      rw [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.baseChange_tmul]
      change q • κ₀ (∑ a : Fin (M + 1), ∑ s : Fin (r a), _) = _
      rw [hΦ y, TensorProduct.tmul_sum]
      simp only [map_sum, hκ₀, TensorProduct.tmul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun s _ => ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hsurj : Function.Surjective ψ := by
    intro d
    suffices h : d ∈ LinearMap.range ψ from h
    induction d using DirectSum.induction_on with
    | zero => exact Submodule.zero_mem _
    | add u v hu hv => exact Submodule.add_mem _ hu hv
    | of a t =>
      change DirectSum.lof ℚ_[l] ℤ T a t ∈ _
      by_cases ha0 : a < 0
      · haveI := hl_sub hA9 l (sch.obj X) a i ha0
        have : t = 0 := by
          induction t using TensorProduct.induction_on with
          | zero => rfl
          | add u v hu hv => rw [hu, hv, add_zero]
          | tmul u v =>
            have : u = 0 := by
              induction u using TensorProduct.induction_on with
              | zero => rfl
              | add u v hu hv => rw [hu, hv, add_zero]
              | tmul q x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
            rw [this, TensorProduct.zero_tmul]
        rw [this, map_zero]; exact Submodule.zero_mem _
      by_cases haM : (M : ℤ) < a
      · haveI := hl_sub hA9 l (sch.obj Y) (n - a) 0 (by omega)
        have : t = 0 := by
          induction t using TensorProduct.induction_on with
          | zero => rfl
          | add u v hu hv => rw [hu, hv, add_zero]
          | tmul u v =>
            have : v = 0 := by
              induction v using TensorProduct.induction_on with
              | zero => rfl
              | add u v hu hv => rw [hu, hv, add_zero]
              | tmul q x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
            rw [this, TensorProduct.tmul_zero]
        rw [this, map_zero]; exact Submodule.zero_mem _
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ a)
      have hm : m < M + 1 := by omega
      have hbase : ∀ (s : Fin (r m)) (q : ℚ_[l]) (y : Hl l (sch.obj Y) (n - (m : ℤ)) 0),
          DirectSum.lof ℚ_[l] ℤ T (m : ℤ) (((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c m s) ⊗ₜ[ℚ_[l]] (q ⊗ₜ[ℤ_[l]] y)) ∈
            LinearMap.range ψ := by
        intro s q y
        refine ⟨q ⊗ₜ[ℤ_[l]] (Pi.single (M := fun a : Fin (M + 1) => Fin (r a) → Hl l (sch.obj Y) (n - ((a : ℕ) : ℤ)) 0)
          ⟨m, hm⟩ (Pi.single s y)), ?_⟩
        rw [LinearMap.liftBaseChange_tmul]
        change q • (∑ a : Fin (M + 1), ∑ s : Fin (r a), _) = _
        rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin (M + 1))]
        · rw [Finset.sum_eq_single s]
          · simp only [Pi.single_eq_same]
            rw [← map_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          · intro s' _ hs'; rw [Pi.single_eq_same, Pi.single_eq_of_ne hs', TensorProduct.tmul_zero,
              TensorProduct.tmul_zero, map_zero]
          · intro h; exact absurd (Finset.mem_univ s) h
        · intro b _ hb
          rw [Pi.single_eq_of_ne hb]
          simp only [Pi.zero_apply, TensorProduct.tmul_zero, map_zero, Finset.sum_const_zero]
        · intro h; exact absurd (Finset.mem_univ _) h
      have hspan := (hB m (by omega)).2
      suffices goal : ∀ t' : HQ l (sch.obj X) (m : ℤ) i ⊗[ℚ_[l]] HQ l (sch.obj Y) (n - (m : ℤ)) 0,
          DirectSum.lof ℚ_[l] ℤ T (m : ℤ) t' ∈ LinearMap.range ψ from goal t
      intro t
      induction t using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add u v hu hv => rw [map_add]; exact Submodule.add_mem _ hu hv
      | tmul u v =>
        have hu : u ∈ Submodule.span ℚ_[l] (Set.range fun s => ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] c m s : HQ l (sch.obj X) (m : ℤ) i)) := by
          rw [hspan]; exact Submodule.mem_top
        induction hu using Submodule.span_induction with
        | mem u hu =>
          obtain ⟨s, rfl⟩ := hu
          induction v using TensorProduct.induction_on with
          | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
          | add v w hv hw => rw [TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ hv hw
          | tmul q y => exact hbase s q y
        | zero => rw [TensorProduct.zero_tmul, map_zero]; exact Submodule.zero_mem _
        | add u w _ _ hu hw => rw [TensorProduct.add_tmul, map_add]; exact Submodule.add_mem _ hu hw
        | smul k u _ hu => rw [← TensorProduct.smul_tmul', map_smul]; exact Submodule.smul_mem _ k hu
  have hbijκ : Function.Bijective κ₀ := by
    constructor
    · rw [injective_iff_map_eq_zero]
      intro d hd
      obtain ⟨u, rfl⟩ := hsurj d
      rw [key] at hd
      have : u = 0 := (injective_iff_map_eq_zero _).mp hbij.1 u hd
      rw [this, map_zero]
    · intro w
      obtain ⟨u, rfl⟩ := hbij.2 w
      exact ⟨ψ u, key u⟩
  exact ⟨LinearEquiv.ofBijective κ₀ hbijκ, fun a x y => hκ₀ a x y⟩

/- English proof (translation)
The claim follows from `limAssembleCut limRatBij limRatAssemble`.
-/
theorem LimAssemble_of : LimAssemble := limAssembleCut limRatBij limRatAssemble

end LateralTheory.KummerTheory

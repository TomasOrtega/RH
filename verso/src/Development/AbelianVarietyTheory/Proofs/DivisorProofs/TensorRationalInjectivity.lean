import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.TensorDevissage

variable {A : Type} [CommRing A] {I : Type} {B : I → Type} [∀ i, CommRing (B i)]

def JointInj (φ : ∀ i, A →+* B i) (L : Type) [AddCommGroup L] : Prop :=
  ∀ h : A ⊗[ℤ] L, (∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0

variable (φ : ∀ i, A →+* B i)

/- English proof (translation)
Rewrite using `[← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]`.
-/
theorem comm_sq {L L' : Type} [AddCommGroup L] [AddCommGroup L'] (g : L →ₗ[ℤ] L') (i : I)
    (h : A ⊗[ℤ] L) :
    LinearMap.rTensor L' (φ i).toAddMonoidHom.toIntLinearMap (LinearMap.lTensor A g h) =
      LinearMap.lTensor (B i) g (LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

/- English proof (translation)
Proceed by induction on `h using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul a l => rw [Subsingleton.elim l 0, tmul_zero]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`.
-/
theorem all_zero_of_subsingleton (L : Type) [AddCommGroup L] [Subsingleton L] (h : A ⊗[ℤ] L) :
    h = 0 := by
  induction h using TensorProduct.induction_on with
  | zero => rfl
  | tmul a l => rw [Subsingleton.elim l 0, tmul_zero]
  | add x y hx hy => rw [hx, hy, add_zero]

/- English proof (translation)
Introduce `h _` and use `all_zero_of_subsingleton L h`.
-/
theorem of_subsingleton (L : Type) [AddCommGroup L] [Subsingleton L] : JointInj φ L :=
  fun h _ => all_zero_of_subsingleton L h

/- English proof (translation)
Introduce `h hh`. Apply `Module.Flat.lTensor_preserves_injective_linearMap (M := A) g hg` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h' _ fun i => by rw [comm_sq, hh i, map_zero]`.
-/
theorem of_injective [Module.Flat ℤ A] {L L' : Type} [AddCommGroup L] [AddCommGroup L']
    (g : L →ₗ[ℤ] L') (hg : Function.Injective g) (h' : JointInj φ L') : JointInj φ L := by
  intro h hh
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := A) g hg
  rw [map_zero]
  exact h' _ fun i => by rw [comm_sq, hh i, map_zero]

/- English proof (translation)
Take `⟨h0, rfl⟩` from `hr`. Rewrite using `[h' h0 fun i => ?_, map_zero]`. Apply `Module.Flat.lTensor_preserves_injective_linearMap (M := B i) g hg` to reduce the goal to its premises. Rewrite using `[map_zero, ← comm_sq, hh i]`.
-/
theorem zero_of_mem_range [∀ i, Module.Flat ℤ (B i)] {L L' : Type} [AddCommGroup L]
    [AddCommGroup L'] (g : L' →ₗ[ℤ] L) (hg : Function.Injective g) (h' : JointInj φ L')
    (h : A ⊗[ℤ] L) (hr : ∃ y, LinearMap.lTensor A g y = h)
    (hh : ∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) : h = 0 := by
  obtain ⟨h0, rfl⟩ := hr
  rw [h' h0 fun i => ?_, map_zero]
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := B i) g hg
  rw [map_zero, ← comm_sq, hh i]

/- English proof (translation)
Introduce `h hh`. Establish `h0 : LinearMap.lTensor A g h = 0` using `h3 _ fun i => by rw [comm_sq, hh i, map_zero]`. Take `⟨y, hy⟩` from `(lTensor_exact A hfg hg h).mp h0`. Conclude with `zero_of_mem_range φ f hf h1 h ⟨y, hy⟩ hh`.
-/
theorem of_exact [∀ i, Module.Flat ℤ (B i)] {L' L L'' : Type} [AddCommGroup L'] [AddCommGroup L]
    [AddCommGroup L''] (f : L' →ₗ[ℤ] L) (g : L →ₗ[ℤ] L'') (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (h1 : JointInj φ L')
    (h3 : JointInj φ L'') : JointInj φ L := by
  intro h hh
  have h0 : LinearMap.lTensor A g h = 0 := h3 _ fun i => by rw [comm_sq, hh i, map_zero]
  obtain ⟨y, hy⟩ := (lTensor_exact A hfg hg h).mp h0
  exact zero_of_mem_range φ f hf h1 h ⟨y, hy⟩ hh

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun a b => by obtain ⟨m, rfl⟩ := ht a obtain ⟨n, rfl⟩ := ht b rw [h0, h0]⟩`.
-/
theorem subsingleton_of_surj {C : Type} [AddCommGroup C] (t : ℤ →ₗ[ℤ] C)
    (ht : Function.Surjective t) (h0 : ∀ n, t n = 0) : Subsingleton C :=
  ⟨fun a b => by
    obtain ⟨m, rfl⟩ := ht a
    obtain ⟨n, rfl⟩ := ht b
    rw [h0, h0]⟩

/- English proof (translation)
Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible`. Distinguish the cases in `htop : LinearMap.ker t = ⊤`. Use `haveI := subsingleton_of_surj t ht fun n => by`. Rewrite using `[LinearMap.ker_eq_top.mp htop]`. Both sides reduce to the same expression.

Conclude with `of_subsingleton φ C`. Establish `hk : LinearMap.ker t = Ideal.span {(p : ℤ)}`. Use `(hmax.eq_of_le htop ?_).symm` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `LinearMap.mem_ker.mpr htp`.

Set `e : C ≃+ ZMod p` to `((t.quotKerEquivOfSurjective ht).symm.toAddEquiv.trans (Submodule.quotEquivOfEq _ _ hk).toAddEquiv).trans (Int.quotientSpanNatEquivZMod p).toAddEquiv`. Conclude with `of_injective φ e.toAddMonoidHom.toIntLinearMap e.injective hP`.
-/
theorem of_prime [Module.Flat ℤ A] (p : ℕ) (hp : p.Prime) (hP : JointInj φ (ZMod p)) {C : Type}
    [AddCommGroup C] (t : ℤ →ₗ[ℤ] C) (ht : Function.Surjective t) (htp : t p = 0) :
    JointInj φ C := by
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  by_cases htop : LinearMap.ker t = ⊤
  · haveI := subsingleton_of_surj t ht fun n => by
      rw [LinearMap.ker_eq_top.mp htop]; rfl
    exact of_subsingleton φ C
  · have hk : LinearMap.ker t = Ideal.span {(p : ℤ)} := by
      refine (hmax.eq_of_le htop ?_).symm
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact LinearMap.mem_ker.mpr htp
    let e : C ≃+ ZMod p := ((t.quotKerEquivOfSurjective ht).symm.toAddEquiv.trans
      (Submodule.quotEquivOfEq _ _ hk).toAddEquiv).trans (Int.quotientSpanNatEquivZMod p).toAddEquiv
    exact of_injective φ e.toAddMonoidHom.toIntLinearMap e.injective hP

/- English proof (translation)
Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `hk C _ t ht htk`. Distinguish the cases in `h1 : k = 1`.

Substitute `h1 haveI := subsingleton_of_surj t ht fun n => by` using the available equality. Rewrite using `[show n = n • (((1 : ℕ) : ℤ)) by simp, map_zsmul, htk, smul_zero]`. Conclude with `of_subsingleton φ C`. Establish `hp : k.minFac.Prime` using `Nat.minFac_prime h1`. Take `⟨m, hm⟩ : k.minFac ∣ k` from `Nat.minFac_dvd k`.

Establish `hp2` using `hp.two_le`. Distinguish the cases in `hm1 : m = 1`. Substitute `hm1` using the available equality. Rewrite `hm` using `[_root_.mul_one]`. Rewrite `htk` using `[hm]`.

Conclude with `of_prime φ _ hp (hP _ hp) t ht htk`. Establish `hm0 : 0 < m`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Substitute `h` using the available equality. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hmk : m < k` using `by nlinarith`. Establish `hpk : k.minFac < k`. Establish `: 2 ≤ m` using `by omega`. Use the polynomial consequences of the given equalities and inequalities.

Set `s : ℤ →ₗ[ℤ] C` to `((k.minFac : ℕ) : ℤ) • t`. Establish `hs1 : JointInj φ (LinearMap.range s)`. Use `ih m hmk hm0 _ s.rangeRestrict s.surjective_rangeRestrict ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [LinearMap.codRestrict_apply, ZeroMemClass.coe_zero, s, LinearMap.rangeRestrict, LinearMap.smul_apply]`.

Rewrite using `[← map_zsmul, smul_eq_mul, ← Nat.cast_mul, ← hm, htk]`. Establish `hs3 : JointInj φ (C ⧸ LinearMap.range s)`. Use `ih _ hpk hp.pos _ ((LinearMap.range s).mkQ ∘ₗ t) ((LinearMap.range s).mkQ_surjective.comp ht) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Use `⟨1, ?_⟩` and prove the remaining obligations.

Simplify using `only [s, LinearMap.smul_apply]`. Rewrite using `[← map_zsmul, smul_eq_mul, _root_.mul_one]`. Conclude with `of_exact φ _ _ (LinearMap.range s).injective_subtype (LinearMap.exact_subtype_mkQ _) (LinearMap.range s).mkQ_surjective hs1 hs3`.
-/
theorem of_killed [Module.Flat ℤ A] [∀ i, Module.Flat ℤ (B i)]
    (hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)) :
    ∀ (k : ℕ), 0 < k → ∀ (C : Type) [AddCommGroup C] (t : ℤ →ₗ[ℤ] C),
      Function.Surjective t → t k = 0 → JointInj φ C := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk C _ t ht htk
  by_cases h1 : k = 1
  · subst h1
    haveI := subsingleton_of_surj t ht fun n => by
      rw [show n = n • (((1 : ℕ) : ℤ)) by simp, map_zsmul, htk, smul_zero]
    exact of_subsingleton φ C
  have hp : k.minFac.Prime := Nat.minFac_prime h1
  obtain ⟨m, hm⟩ : k.minFac ∣ k := Nat.minFac_dvd k
  have hp2 := hp.two_le
  by_cases hm1 : m = 1
  · subst hm1
    rw [_root_.mul_one] at hm
    rw [hm] at htk
    exact of_prime φ _ hp (hP _ hp) t ht htk
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; omega
    · exact h
  have hmk : m < k := by nlinarith
  have hpk : k.minFac < k := by
    have : 2 ≤ m := by omega
    nlinarith
  let s : ℤ →ₗ[ℤ] C := ((k.minFac : ℕ) : ℤ) • t
  have hs1 : JointInj φ (LinearMap.range s) := by
    refine ih m hmk hm0 _ s.rangeRestrict s.surjective_rangeRestrict ?_
    apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, ZeroMemClass.coe_zero, s, LinearMap.rangeRestrict,
      LinearMap.smul_apply]
    rw [← map_zsmul, smul_eq_mul, ← Nat.cast_mul, ← hm, htk]
  have hs3 : JointInj φ (C ⧸ LinearMap.range s) := by
    refine ih _ hpk hp.pos _ ((LinearMap.range s).mkQ ∘ₗ t)
      ((LinearMap.range s).mkQ_surjective.comp ht) ?_
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨1, ?_⟩
    simp only [s, LinearMap.smul_apply]
    rw [← map_zsmul, smul_eq_mul, _root_.mul_one]
  exact of_exact φ _ _ (LinearMap.range s).injective_subtype
    (LinearMap.exact_subtype_mkQ _) (LinearMap.range s).mkQ_surjective hs1 hs3

end GlobalTheory.TensorDevissage

/- English proof (translation)
Proceed by induction on `h using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul a l => rw [Subsingleton.elim a 0, zero_tmul]`. Consider the case `add x y hx hy => rw [hx, hy, add_zero]`.
-/
theorem GlobalTheory.TensorDevissage.all_zero_of_subsingleton' {A L : Type} [CommRing A] [Subsingleton A]
    [AddCommGroup L] (h : A ⊗[ℤ] L) : h = 0 := by
  induction h using TensorProduct.induction_on with
  | zero => rfl
  | tmul a l => rw [Subsingleton.elim a 0, zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

namespace GlobalTheory.TensorDevissage

variable {A : Type} [CommRing A] {I : Type} {B : I → Type} [∀ i, CommRing (B i)]
variable (φ : ∀ i, A →+* B i)

/- English proof (translation)
Distinguish the cases in `hex : ∃ k : ℕ, 0 < k ∧ t k = 0`. Take `⟨k, hk, htk⟩` from `hex`. Conclude with `of_killed φ hP k hk C t ht htk`. Use `push_neg at hex`. Establish `hinj : Function.Injective t`.

Use `(injective_iff_map_eq_zero t).mpr fun n hn => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Apply `hex n.natAbs (Int.natAbs_pos.mpr hne)` to reduce the goal to its premises. Break down `Int.natAbs_eq n with h | h` into its components or cases. Rewrite using `[← h]`.

Conclude with `hn`. Rewrite using `[show ((n.natAbs : ℕ) : ℤ) = -n by omega, map_neg, hn, neg_zero]`. Set `e` to `LinearEquiv.ofBijective t ⟨hinj, ht⟩`. Conclude with `of_injective φ e.symm.toLinearMap e.symm.injective hZ`.
-/
theorem of_cyclic [Module.Flat ℤ A] [∀ i, Module.Flat ℤ (B i)] (hZ : JointInj φ ℤ)
    (hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)) (C : Type) [AddCommGroup C] (t : ℤ →ₗ[ℤ] C)
    (ht : Function.Surjective t) : JointInj φ C := by
  by_cases hex : ∃ k : ℕ, 0 < k ∧ t k = 0
  · obtain ⟨k, hk, htk⟩ := hex
    exact of_killed φ hP k hk C t ht htk
  · push_neg at hex
    have hinj : Function.Injective t := by
      refine (injective_iff_map_eq_zero t).mpr fun n hn => ?_
      by_contra hne
      apply hex n.natAbs (Int.natAbs_pos.mpr hne)
      rcases Int.natAbs_eq n with h | h
      · rw [← h]; exact hn
      · rw [show ((n.natAbs : ℕ) : ℤ) = -n by omega, map_neg, hn, neg_zero]
    let e := LinearEquiv.ofBijective t ⟨hinj, ht⟩
    exact of_injective φ e.symm.toLinearMap e.symm.injective hZ

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `L _ s hs hspan`. Rewrite `hs` using `[Nat.le_zero, Finset.card_eq_zero]`.

Substitute `hs` using the available equality. Use `haveI : Subsingleton L := ⟨fun a b => by`. Establish `ha : a ∈ Submodule.span ℤ ((∅ : Finset L) : Set L)` using `hspan ▸ Submodule.mem_top`. Establish `hb : b ∈ Submodule.span ℤ ((∅ : Finset L) : Set L)` using `hspan ▸ Submodule.mem_top`. Rewrite `ha`, `hb` using `[Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot]`.

Rewrite using `[ha, hb]⟩`. Conclude with `of_subsingleton φ L`. Consider the case `succ n ih`. Introduce `L _ s hs hspan`. Break down `s.eq_empty_or_nonempty with h | ⟨x, hx⟩` into its components or cases.

Substitute `h` using the available equality. Conclude with `ih L ∅ (by simp) hspan`. Establish `h1 : JointInj φ (LinearMap.range (LinearMap.toSpanSingleton ℤ L x))` using `of_cyclic φ hZ hP _ _ (LinearMap.surjective_rangeRestrict _)`. Establish `h3 : JointInj φ (L ⧸ LinearMap.range (LinearMap.toSpanSingleton ℤ L x))`. Use `ih _ ((s.erase x).image (LinearMap.range (LinearMap.toSpanSingleton ℤ L x)).mkQ) (Finset.card_image_le.trans ?_) ?_` and prove the remaining obligations.

Use `Finset.card_erase_of_mem hx` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.coe_image, ← Submodule.map_span, Submodule.map_mkQ_eq_top, ← LinearMap.span_singleton_eq_range, ← Submodule.span_insert, Finset.coe_erase, Set.insert_diff_singleton, Set.insert_eq_of_mem (by exact_mod_cast hx), hspan]`. Conclude with `of_exact φ _ _ (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ _) (Submodule.mkQ_surjective _) h1 h3`.
-/
theorem of_fg [Module.Flat ℤ A] [∀ i, Module.Flat ℤ (B i)] (hZ : JointInj φ ℤ)
    (hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)) :
    ∀ (n : ℕ) (L : Type) [AddCommGroup L] (s : Finset L), s.card ≤ n →
      Submodule.span ℤ (s : Set L) = ⊤ → JointInj φ L := by
  classical
  intro n
  induction n with
  | zero =>
    intro L _ s hs hspan
    rw [Nat.le_zero, Finset.card_eq_zero] at hs
    subst hs
    haveI : Subsingleton L := ⟨fun a b => by
      have ha : a ∈ Submodule.span ℤ ((∅ : Finset L) : Set L) := hspan ▸ Submodule.mem_top
      have hb : b ∈ Submodule.span ℤ ((∅ : Finset L) : Set L) := hspan ▸ Submodule.mem_top
      rw [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at ha hb
      rw [ha, hb]⟩
    exact of_subsingleton φ L
  | succ n ih =>
    intro L _ s hs hspan
    rcases s.eq_empty_or_nonempty with h | ⟨x, hx⟩
    · subst h
      exact ih L ∅ (by simp) hspan
    have h1 : JointInj φ (LinearMap.range (LinearMap.toSpanSingleton ℤ L x)) :=
      of_cyclic φ hZ hP _ _ (LinearMap.surjective_rangeRestrict _)
    have h3 : JointInj φ (L ⧸ LinearMap.range (LinearMap.toSpanSingleton ℤ L x)) := by
      refine ih _ ((s.erase x).image (LinearMap.range (LinearMap.toSpanSingleton ℤ L x)).mkQ)
        (Finset.card_image_le.trans ?_) ?_
      · have := Finset.card_erase_of_mem hx
        omega
      · rw [Finset.coe_image, ← Submodule.map_span, Submodule.map_mkQ_eq_top,
          ← LinearMap.span_singleton_eq_range, ← Submodule.span_insert, Finset.coe_erase,
          Set.insert_diff_singleton, Set.insert_eq_of_mem (by exact_mod_cast hx), hspan]
    exact of_exact φ _ _ (Submodule.injective_subtype _) (LinearMap.exact_subtype_mkQ _)
      (Submodule.mkQ_surjective _) h1 h3

/- English proof (translation)
Introduce `h hh`. Take `⟨L0, hfin, hsub⟩` from `TensorProduct.exists_finite_submodule_right_of_setFinite {h} (Set.finite_singleton h)`. Take `⟨s, hs⟩` from `hfin.fg_top`. Establish `h0 : JointInj φ L0` using `of_fg φ hZ hP s.card L0 s le_rfl hs`. Take `⟨y, hy⟩` from `LinearMap.mem_range.mp (hsub (Set.mem_singleton h))`.

Conclude with `zero_of_mem_range φ L0.subtype (Submodule.injective_subtype _) h0 h ⟨y, hy⟩ hh`.
-/
theorem of_all [Module.Flat ℤ A] [∀ i, Module.Flat ℤ (B i)] (hZ : JointInj φ ℤ)
    (hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)) (L : Type) [AddCommGroup L] :
    JointInj φ L := by
  intro h hh
  obtain ⟨L0, hfin, hsub⟩ :=
    TensorProduct.exists_finite_submodule_right_of_setFinite {h} (Set.finite_singleton h)
  obtain ⟨s, hs⟩ := hfin.fg_top
  have h0 : JointInj φ L0 := of_fg φ hZ hP s.card L0 s le_rfl hs
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (hsub (Set.mem_singleton h))
  exact zero_of_mem_range φ L0.subtype (Submodule.injective_subtype _) h0 h ⟨y, hy⟩ hh

end GlobalTheory.TensorDevissage

namespace GlobalTheory

open GlobalTheory.TensorDevissage in

/- English proof (translation)
Introduce `N I A _ B _ φ hA hB hN hQ hp L _ h hh`. Use `haveI := hA`. Use `haveI := hB`. Distinguish the cases in `hN0 : N = 0`. Substitute `hN0 haveI : Subsingleton A := by` using the available equality.

Establish `: IsUnit (0 : A)` using `by simpa using hN`. Conclude with `subsingleton_of_zero_eq_one (isUnit_zero_iff.mp this)`. Conclude with `all_zero_of_subsingleton' h`. Establish `hZ : JointInj φ ℤ` using `of_injective φ (Int.castAddHom ℚ).toIntLinearMap Int.cast_injective (hQ hN0)`. Establish `hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p)`.

Introduce `p hpp`. Distinguish the cases in `hpN : p ∣ N`. Introduce `x _`. Establish `hkill : ∀ y : A ⊗[ℤ] ZMod p, (N : ℤ) • y = 0`. Introduce `y`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a z`. Rewrite using `[← TensorProduct.tmul_smul, zsmul_eq_mul, Int.cast_natCast]`. Take `⟨c, rfl⟩` from `hpN`.

Rewrite using `[Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul, tmul_zero]`. Consider the case `add y1 y2 h1 h2 => rw [smul_add, h1, h2, add_zero]`. Take `⟨u, hu⟩` from `hN`. Establish `hx : x = ((u⁻¹ : Aˣ) : A) • (((N : ℤ) : A) • x)`. Rewrite using `[smul_smul, ← hu, Units.inv_mul, one_smul]`.

Rewrite using `[hx, Int.cast_smul_eq_zsmul, hkill, smul_zero]`. Conclude with `hp p hpp hpN`. Conclude with `of_all φ hZ hP L h hh`.
-/
theorem jointInj_tensor_of_rat_and_zmod : ∀ (N : ℕ) (I A : Type) [CommRing A] (B : I → Type) [∀ i, CommRing (B i)] (φ : ∀ i, A →+* B i),
    Module.Flat ℤ A → (∀ i, Module.Flat ℤ (B i)) → IsUnit ((N : ℤ) : A) →
    (N ≠ 0 → ∀ h : A ⊗[ℤ] ℚ, (∀ i, LinearMap.rTensor ℚ (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ h : A ⊗[ℤ] ZMod p,
      (∀ i, LinearMap.rTensor (ZMod p) (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0) →
    ∀ (L : Type) [AddCommGroup L] (h : A ⊗[ℤ] L),
      (∀ i, LinearMap.rTensor L (φ i).toAddMonoidHom.toIntLinearMap h = 0) → h = 0 := by
  intro N I A _ B _ φ hA hB hN hQ hp L _ h hh
  haveI := hA
  haveI := hB
  by_cases hN0 : N = 0
  · subst hN0
    haveI : Subsingleton A := by
      have : IsUnit (0 : A) := by simpa using hN
      exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp this)
    exact all_zero_of_subsingleton' h
  have hZ : JointInj φ ℤ :=
    of_injective φ (Int.castAddHom ℚ).toIntLinearMap Int.cast_injective (hQ hN0)
  have hP : ∀ p : ℕ, p.Prime → JointInj φ (ZMod p) := by
    intro p hpp
    by_cases hpN : p ∣ N
    · intro x _
      have hkill : ∀ y : A ⊗[ℤ] ZMod p, (N : ℤ) • y = 0 := by
        intro y
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul a z =>
          rw [← TensorProduct.tmul_smul, zsmul_eq_mul, Int.cast_natCast]
          obtain ⟨c, rfl⟩ := hpN
          rw [Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_mul, tmul_zero]
        | add y1 y2 h1 h2 => rw [smul_add, h1, h2, add_zero]
      obtain ⟨u, hu⟩ := hN
      have hx : x = ((u⁻¹ : Aˣ) : A) • (((N : ℤ) : A) • x) := by
        rw [smul_smul, ← hu, Units.inv_mul, one_smul]
      rw [hx, Int.cast_smul_eq_zsmul, hkill, smul_zero]
    · exact hp p hpp hpN
  exact of_all φ hZ hP L h hh

end GlobalTheory

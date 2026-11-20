import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal

open TensorProduct LinearMap IsLocalRing

namespace PositivityTheory.HtPt.Pfib

open GlobalTheory.LocalFlat

/- English proof (translation)
Set `I` to `p.map (algebraMap R A)`. Set `c : p →ₗ[R] I` to `{ toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩ map_add' := fun r s => Subtype.ext (by simp) map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }`. Set `φ : M ⊗[R] p →ₗ[R] M ⊗[A] I` to `TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M`. Establish `hφ : ∀ m r, φ (m ⊗ₜ r) = m ⊗ₜ[A] c r` using `fun _ _ => rfl`. Establish `hsurj : ∀ x, x ∈ LinearMap.range φ`.

Introduce `x`. Proceed by induction on `x with`. Consider the case `zero => exact zero_mem _`. Consider the case `add a b ha hb => exact add_mem ha hb`. Consider the case `tmul m i`.

Take `⟨i, hi⟩` from `i`. Proceed by induction on `hi using Submodule.span_induction generalizing m with`. Consider the case `mem x hx`. Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩`.

Consider the case `zero`. Express the relevant statement in the definitionally equal form `m ⊗ₜ[A] (0 : I) ∈ _`. Rewrite using `[tmul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y hx hy ihx ihy`.

Express the relevant statement in the definitionally equal form `m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _`. Rewrite using `[tmul_add]`. Conclude with `add_mem (ihx m) (ihy m)`. Consider the case `smul a x hx ih`. Express the relevant statement in the definitionally equal form `m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _`.

Rewrite using `[← smul_tmul]`. Conclude with `ih _`. Establish `hcomp : ∀ y, TensorProduct.rid A M (I.subtype.lTensor M (φ y)) = TensorProduct.rid R M (p.subtype.lTensor M y)`. Introduce `y`. Proceed by induction on `y with`.

Consider the case `zero => simp`. Consider the case `add a b ha hb => simp only [map_add, ha, hb]`. Consider the case `tmul m r => simp [hφ, c]`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`.

Take `⟨y, rfl⟩` from `hsurj x`. Establish `h0` using `hcomp y`. Rewrite `h0` using `[hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective, map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype p.injective_subtype)]`. Rewrite using `[h0, map_zero]`.
-/
theorem lTensor_map_injective {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Flat R M]
    (p : Ideal R) :
    Function.Injective ((p.map (algebraMap R A)).subtype.lTensor M) := by
  let I := p.map (algebraMap R A)
  let c : p →ₗ[R] I :=
    { toFun := fun r => ⟨algebraMap R A r, Ideal.mem_map_of_mem _ r.2⟩
      map_add' := fun r s => Subtype.ext (by simp)
      map_smul' := fun r s => Subtype.ext (by simp [Algebra.smul_def]) }
  let φ : M ⊗[R] p →ₗ[R] M ⊗[A] I :=
    TensorProduct.mapOfCompatibleSMul A R R M I ∘ₗ c.lTensor M
  have hφ : ∀ m r, φ (m ⊗ₜ r) = m ⊗ₜ[A] c r := fun _ _ => rfl
  have hsurj : ∀ x, x ∈ LinearMap.range φ := by
    intro x
    induction x with
    | zero => exact zero_mem _
    | add a b ha hb => exact add_mem ha hb
    | tmul m i =>
      obtain ⟨i, hi⟩ := i
      induction hi using Submodule.span_induction generalizing m with
      | mem x hx =>
        obtain ⟨r, hr, rfl⟩ := hx
        exact ⟨m ⊗ₜ ⟨r, hr⟩, rfl⟩
      | zero =>
        change m ⊗ₜ[A] (0 : I) ∈ _
        rw [tmul_zero]
        exact zero_mem _
      | add x y hx hy ihx ihy =>
        change m ⊗ₜ[A] ((⟨x, hx⟩ : I) + ⟨y, hy⟩) ∈ _
        rw [tmul_add]
        exact add_mem (ihx m) (ihy m)
      | smul a x hx ih =>
        change m ⊗ₜ[A] (a • (⟨x, hx⟩ : I)) ∈ _
        rw [← smul_tmul]
        exact ih _
  have hcomp : ∀ y, TensorProduct.rid A M (I.subtype.lTensor M (φ y)) =
      TensorProduct.rid R M (p.subtype.lTensor M y) := by
    intro y
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul m r => simp [hφ, c]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  have h0 := hcomp y
  rw [hx, map_zero, eq_comm, map_eq_zero_iff _ (TensorProduct.rid R M).injective,
    map_eq_zero_iff _ (Module.Flat.lTensor_preserves_injective_linearMap p.subtype
      p.injective_subtype)] at h0
  rw [h0, map_zero]

section Devissage

variable {A : Type} [CommRing A] {M : Type} [AddCommGroup M] [Module A M]

/- English proof (translation)
Establish `hex` using `lTensor_exact M (f.coprod g).exact_subtype_ker_map hs`. Establish `h0 : (f.coprod g).lTensor M ((inl A F G).lTensor M x + (inr A F G).lTensor M y) = 0`. Rewrite using `[map_add, ← lTensor_comp_apply, ← lTensor_comp_apply, coprod_inl, coprod_inr, h]`. Take `⟨z, hz⟩` from `(hex _).mp h0`. Use `⟨z, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[lTensor_comp_apply, hz, map_add, ← lTensor_comp_apply, ← lTensor_comp_apply, fst_comp_inl, fst_comp_inr]`. Simplify using the standard rewrite rules. Rewrite using `[lTensor_comp_apply, hz, map_add, ← lTensor_comp_apply, ← lTensor_comp_apply, snd_comp_inl, snd_comp_inr]`. Simplify using the standard rewrite rules.
-/
theorem exists_of_lTensor_eq {F G N : Type} [AddCommGroup F] [Module A F] [AddCommGroup G]
    [Module A G] [AddCommGroup N] [Module A N] (f : F →ₗ[A] N) (g : G →ₗ[A] N)
    (hs : Function.Surjective (f.coprod g)) (x : M ⊗[A] F) (y : M ⊗[A] G)
    (h : f.lTensor M x + g.lTensor M y = 0) :
    ∃ z : M ⊗[A] ker (f.coprod g),
      (fst A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = x ∧
      (snd A F G ∘ₗ (ker (f.coprod g)).subtype).lTensor M z = y := by
  have hex := lTensor_exact M (f.coprod g).exact_subtype_ker_map hs
  have h0 : (f.coprod g).lTensor M ((inl A F G).lTensor M x + (inr A F G).lTensor M y) = 0 := by
    rw [map_add, ← lTensor_comp_apply, ← lTensor_comp_apply, coprod_inl, coprod_inr, h]
  obtain ⟨z, hz⟩ := (hex _).mp h0
  refine ⟨z, ?_, ?_⟩
  · rw [lTensor_comp_apply, hz, map_add, ← lTensor_comp_apply, ← lTensor_comp_apply,
      fst_comp_inl, fst_comp_inr]
    simp
  · rw [lTensor_comp_apply, hz, map_add, ← lTensor_comp_apply, ← lTensor_comp_apply,
      snd_comp_inl, snd_comp_inr]
    simp

/- English proof (translation)
Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨y, rfl⟩` from `hrel F f x (by rw [hx]; simp)`. Set `e₀ : Submodule.comap f I →ₗ[A] I` to `f.restrict fun _ h => h`. Establish `he : Function.Bijective e₀`.

Use `⟨fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)), fun i => ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `hle i.2`. Conclude with `⟨⟨a, by rw [Submodule.mem_comap, ha]; exact i.2⟩, Subtype.ext ha⟩`. Set `e` to `LinearEquiv.ofBijective e₀ he`. Establish `hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0`.

Rewrite using `[← hx, ← lTensor_comp_apply, ← lTensor_comp_apply]`. Both sides reduce to the same expression. Rewrite `hy` using `[map_eq_zero_iff _ hI]`. Establish `: y = 0` using `(LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)`. Rewrite using `[this, map_zero]`.
-/
theorem lTensor_injective_of_le_range {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) {F : Type} [AddCommGroup F] [Module A F]
    (f : F →ₗ[A] A) (hf : Function.Injective f) (hle : I ≤ range f) :
    Function.Injective (f.lTensor M) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := hrel F f x (by rw [hx]; simp)
  let e₀ : Submodule.comap f I →ₗ[A] I := f.restrict fun _ h => h
  have he : Function.Bijective e₀ := by
    refine ⟨fun a b hab => Subtype.ext (hf (congrArg Subtype.val hab)), fun i => ?_⟩
    obtain ⟨a, ha⟩ := hle i.2
    exact ⟨⟨a, by rw [Submodule.mem_comap, ha]; exact i.2⟩, Subtype.ext ha⟩
  let e := LinearEquiv.ofBijective e₀ he
  have hy : I.subtype.lTensor M (e.toLinearMap.lTensor M y) = 0 := by
    rw [← hx, ← lTensor_comp_apply, ← lTensor_comp_apply]
    rfl
  rw [map_eq_zero_iff _ hI] at hy
  have : y = 0 := (LinearEquiv.lTensor M e).injective (hy.trans (map_zero _).symm)
  rw [this, map_zero]

/- English proof (translation)
Proceed by induction on `J using WellFoundedGT.induction with`. Consider the case `ind J ih`. Distinguish the cases in `hex : ∃ a, a ∉ J ∧ ∀ i ∈ I, i * a ∈ J`. Take `⟨a, ha, hIa⟩` from `hex`. Set `J' : Ideal A` to `J ⊔ Ideal.span {a}`.

Establish `haJ' : a ∈ J'` using `Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)`. Establish `hlt : J < J'` using `lt_of_le_of_ne le_sup_left fun h => ha (h ▸ haJ')`. Establish `h'` using `ih J' hlt (hJ.trans hlt.le)`. Set `f : J →ₗ[A] J'` to `Submodule.inclusion hlt.le`. Set `g : A →ₗ[A] J'` to `toSpanSingleton A J' ⟨a, haJ'⟩`.

Establish `hs : Function.Surjective (f.coprod g)`. Introduce and unpack `⟨b, hb⟩`. Take `⟨j, hj, c, hc, rfl⟩` from `Submodule.mem_sup.mp hb`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.mp hc`. Conclude with `⟨(⟨j, hj⟩, c), rfl⟩`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `hfx : f.lTensor M x = 0`. Apply `h'` to reduce the goal to its premises. Rewrite using `[← lTensor_comp_apply, map_zero]`.

Conclude with `hx`. Take `⟨z, hz1, hz2⟩` from `exists_of_lTensor_eq f g hs x 0 (by rw [hfx, map_zero, add_zero])`. Establish `hinj : Function.Injective ((snd A J A ∘ₗ (ker (f.coprod g)).subtype).lTensor M)`. Use `lTensor_injective_of_le_range hrel hI _ ?_ fun i hi => ?_` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce and unpack `⟨⟨j, c⟩, hjc⟩ hc`. Establish `hc' : c = 0` using `hc`. Substitute `hc'` using the available equality. Establish `h1 : (j : A) + (0 : A) • a = 0` using `congrArg Subtype.val hjc`. Establish `h2 : j = 0` using `Subtype.ext (by simpa using h1)`.

Substitute `h2` using the available equality. Both sides reduce to the same expression. Use `⟨⟨(⟨-(i * a), neg_mem (hIa i hi)⟩, i), ?_⟩, rfl⟩` and prove the remaining obligations. Use `Subtype.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-(i * a) + i • a = 0`.

Simplify using the standard rewrite rules. Establish `hz : z = 0` using `hinj (hz2.trans (map_zero _).symm)`. Rewrite using `[← hz1, hz, map_zero]`. Use `push Not at hex`. Establish `htop : ∀ m : ℕ, I ^ m ≤ J → (1 : A) ∈ J`.

Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro h; exact h (by simp)`. Consider the case `succ m ihm`. Introduce `h`.

Use `ihm fun a ha => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `haJ`. Take `⟨i, hi, hia⟩` from `hex a haJ`. Conclude with `hia (h (by rw [pow_succ']; exact Ideal.mul_mem_mul hi ha))`. Use `lTensor_injective_of_le_range hrel hI _ J.injective_subtype ?_` and prove the remaining obligations.

Rewrite using `[Submodule.range_subtype, (Ideal.eq_top_iff_one J).mpr (htop n hJ)]`. Conclude with `le_top`.
-/
theorem lTensor_injective_of_pow_le [IsNoetherianRing A] {I : Ideal A} (hrel : RelationsLift I M)
    (hI : Function.Injective (I.subtype.lTensor M)) (n : ℕ) (J : Ideal A) (hJ : I ^ n ≤ J) :
    Function.Injective (J.subtype.lTensor M) := by
  induction J using WellFoundedGT.induction with
  | ind J ih =>
  by_cases hex : ∃ a, a ∉ J ∧ ∀ i ∈ I, i * a ∈ J
  · obtain ⟨a, ha, hIa⟩ := hex
    let J' : Ideal A := J ⊔ Ideal.span {a}
    have haJ' : a ∈ J' := Submodule.mem_sup_right (Ideal.mem_span_singleton_self a)
    have hlt : J < J' := lt_of_le_of_ne le_sup_left fun h => ha (h ▸ haJ')
    have h' := ih J' hlt (hJ.trans hlt.le)
    let f : J →ₗ[A] J' := Submodule.inclusion hlt.le
    let g : A →ₗ[A] J' := toSpanSingleton A J' ⟨a, haJ'⟩
    have hs : Function.Surjective (f.coprod g) := by
      rintro ⟨b, hb⟩
      obtain ⟨j, hj, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      exact ⟨(⟨j, hj⟩, c), rfl⟩
    rw [injective_iff_map_eq_zero]
    intro x hx
    have hfx : f.lTensor M x = 0 := by
      apply h'
      rw [← lTensor_comp_apply, map_zero]
      exact hx
    obtain ⟨z, hz1, hz2⟩ := exists_of_lTensor_eq f g hs x 0 (by rw [hfx, map_zero, add_zero])
    have hinj : Function.Injective
        ((snd A J A ∘ₗ (ker (f.coprod g)).subtype).lTensor M) := by
      refine lTensor_injective_of_le_range hrel hI _ ?_ fun i hi => ?_
      · rw [injective_iff_map_eq_zero]
        rintro ⟨⟨j, c⟩, hjc⟩ hc
        have hc' : c = 0 := hc
        subst hc'
        have h1 : (j : A) + (0 : A) • a = 0 := congrArg Subtype.val hjc
        have h2 : j = 0 := Subtype.ext (by simpa using h1)
        subst h2
        rfl
      · refine ⟨⟨(⟨-(i * a), neg_mem (hIa i hi)⟩, i), ?_⟩, rfl⟩
        refine Subtype.ext ?_
        change -(i * a) + i • a = 0
        simp
    have hz : z = 0 := hinj (hz2.trans (map_zero _).symm)
    rw [← hz1, hz, map_zero]
  · push Not at hex
    have htop : ∀ m : ℕ, I ^ m ≤ J → (1 : A) ∈ J := by
      intro m
      induction m with
      | zero => intro h; exact h (by simp)
      | succ m ihm =>
        intro h
        refine ihm fun a ha => ?_
        by_contra haJ
        obtain ⟨i, hi, hia⟩ := hex a haJ
        exact hia (h (by rw [pow_succ']; exact Ideal.mul_mem_mul hi ha))
    refine lTensor_injective_of_le_range hrel hI _ J.injective_subtype ?_
    rw [Submodule.range_subtype, (Ideal.eq_top_iff_one J).mpr (htop n hJ)]
    exact le_top

/- English proof (translation)
Introduce `F _ _ f x hx`. Establish `hy : ∀ m ∈ J • (⊤ : Submodule A M), ∃ y : M ⊗[A] J, TensorProduct.rid A M (J.subtype.lTensor M y) = m`. Introduce `m hm`. Proceed by induction on `hm using Submodule.smul_induction_on' with`. Consider the case `smul r hr m _ => exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩`.

Consider the case `add a _ b _ ha hb`. Take `⟨a', rfl⟩` from `ha`. Take `⟨b', rfl⟩` from `hb`. Conclude with `⟨a' + b', by simp⟩`. Take `⟨y, hy⟩` from `hy _ hx`.

Establish `hy'` using `(TensorProduct.rid A M).injective hy`. Set `J' : Ideal A` to `range f ⊔ J`. Set `f' : F →ₗ[A] J'` to `f.codRestrict J' fun a => Submodule.mem_sup_left ⟨a, rfl⟩`. Set `g : J →ₗ[A] J'` to `Submodule.inclusion le_sup_right`. Establish `hs : Function.Surjective (f'.coprod g)`.

Introduce and unpack `⟨b, hb⟩`. Take `⟨_, ⟨a, rfl⟩, c, hc, rfl⟩` from `Submodule.mem_sup.mp hb`. Conclude with `⟨(a, ⟨c, hc⟩), rfl⟩`. Establish `h0 : f'.lTensor M x + g.lTensor M (-y) = 0`. Apply `h J' le_sup_right` to reduce the goal to its premises.

Rewrite using `[map_add, ← lTensor_comp_apply, ← lTensor_comp_apply, map_zero, map_neg]`. Express the relevant statement in the definitionally equal form `f.lTensor M x + -(J.subtype.lTensor M y) = 0`. Rewrite using `[hy', add_neg_cancel]`. Take `⟨z, hz, -⟩` from `exists_of_lTensor_eq f' g hs x (-y) h0`. Use `range_lTensor_le _ _ ?_ ⟨z, hz⟩` and prove the remaining obligations.

Introduce and unpack `⟨⟨a, j⟩, haj⟩`. Establish `h1 : f a + (j : A) = 0` using `congrArg Subtype.val haj`. Express the relevant statement in the definitionally equal form `f a ∈ J`. Rewrite using `[eq_neg_of_add_eq_zero_left h1]`. Conclude with `neg_mem j.2`.
-/
theorem relationsLift_of_injective {J : Ideal A}
    (h : ∀ J' : Ideal A, J ≤ J' → Function.Injective (J'.subtype.lTensor M)) :
    RelationsLift J M := by
  intro F _ _ f x hx
  have hy : ∀ m ∈ J • (⊤ : Submodule A M),
      ∃ y : M ⊗[A] J, TensorProduct.rid A M (J.subtype.lTensor M y) = m := by
    intro m hm
    induction hm using Submodule.smul_induction_on' with
    | smul r hr m _ => exact ⟨m ⊗ₜ ⟨r, hr⟩, by simp⟩
    | add a _ b _ ha hb =>
      obtain ⟨a', rfl⟩ := ha
      obtain ⟨b', rfl⟩ := hb
      exact ⟨a' + b', by simp⟩
  obtain ⟨y, hy⟩ := hy _ hx
  have hy' := (TensorProduct.rid A M).injective hy
  let J' : Ideal A := range f ⊔ J
  let f' : F →ₗ[A] J' := f.codRestrict J' fun a => Submodule.mem_sup_left ⟨a, rfl⟩
  let g : J →ₗ[A] J' := Submodule.inclusion le_sup_right
  have hs : Function.Surjective (f'.coprod g) := by
    rintro ⟨b, hb⟩
    obtain ⟨_, ⟨a, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.mp hb
    exact ⟨(a, ⟨c, hc⟩), rfl⟩
  have h0 : f'.lTensor M x + g.lTensor M (-y) = 0 := by
    apply h J' le_sup_right
    rw [map_add, ← lTensor_comp_apply, ← lTensor_comp_apply, map_zero, map_neg]
    change f.lTensor M x + -(J.subtype.lTensor M y) = 0
    rw [hy', add_neg_cancel]
  obtain ⟨z, hz, -⟩ := exists_of_lTensor_eq f' g hs x (-y) h0
  refine range_lTensor_le _ _ ?_ ⟨z, hz⟩
  rintro ⟨⟨a, j⟩, haj⟩
  have h1 : f a + (j : A) = 0 := congrArg Subtype.val haj
  change f a ∈ J
  rw [eq_neg_of_add_eq_zero_left h1]
  exact neg_mem j.2

/- English proof (translation)
The claim follows from `flat_of_relationsLift B hI fun n => relationsLift_of_injective fun J hJ => lTensor_injective_of_pow_le hrel hinj n J hJ`.
-/
theorem flat_of_relationsLift_of_injective [IsNoetherianRing A] (B : Type) [CommRing B]
    [Algebra A B] [IsNoetherianRing B] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    {I : Ideal A} (hI : I.map (algebraMap A B) ≤ Ideal.jacobson ⊥) (hrel : RelationsLift I M)
    (hinj : Function.Injective (I.subtype.lTensor M)) : Module.Flat A M :=
  flat_of_relationsLift B hI fun n =>
    relationsLift_of_injective fun J hJ => lTensor_injective_of_pow_le hrel hinj n J hJ

end Devissage

/- English proof (translation)
Introduce `R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB h`. Use `flat_of_relationsLift_of_injective B (I := (maximalIdeal R).map (algebraMap R A)) ?_ ?_ (lTensor_map_injective _)` and prove the remaining obligations. Conclude with `((Ideal.map_mono (map_maximalIdeal_le _)).trans (map_maximalIdeal_le _)).trans (maximalIdeal_le_jacobson _)`. Use `relationsLift_of_square ((Algebra.TensorProduct.includeRight : A →ₐ[R] ResidueField R ⊗[R] A) : A →+* ResidueField R ⊗[R] A) ((Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) : B →+* ResidueField R ⊗[R] B) _ (Algebra.TensorProduct.includeRight_surjective _ res …` and prove the remaining obligations. Rewrite using `[Ideal.map_map, ← IsScalarTower.algebraMap_eq]`.

Conclude with `GlobalTheory.ker_includeRight_quotient B (maximalIdeal R)`. Use extensionality with `a`. Simplify using the standard rewrite rules.
-/
theorem fibre_crit_ring : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hB h
  refine flat_of_relationsLift_of_injective B (I := (maximalIdeal R).map (algebraMap R A)) ?_ ?_
    (lTensor_map_injective _)
  · exact ((Ideal.map_mono (map_maximalIdeal_le _)).trans (map_maximalIdeal_le _)).trans
      (maximalIdeal_le_jacobson _)
  · refine relationsLift_of_square
      ((Algebra.TensorProduct.includeRight : A →ₐ[R] ResidueField R ⊗[R] A) :
        A →+* ResidueField R ⊗[R] A)
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] ResidueField R ⊗[R] B) :
        B →+* ResidueField R ⊗[R] B) _
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (Algebra.TensorProduct.includeRight_surjective _ residue_surjective)
      (GlobalTheory.ker_includeRight_quotient A (maximalIdeal R)) ?_ ?_ h
    · rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
      exact GlobalTheory.ker_includeRight_quotient B (maximalIdeal R)
    · ext a
      simp

end PositivityTheory.HtPt.Pfib

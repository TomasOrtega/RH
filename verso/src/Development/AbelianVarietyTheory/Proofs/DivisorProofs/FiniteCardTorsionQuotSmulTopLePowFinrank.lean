import Mathlib

open scoped TensorProduct

namespace GlobalTheory.TorsionCount

variable {R : Type} [CommRing R] [IsDedekindDomain R]

/- English proof (translation)
Distinguish the cases in `hle : J ≤ I`. Take `⟨J', rfl⟩` from `Ideal.dvd_iff_le.2 hle`. Establish `hJ' : J' ≠ ⊥` using `by rintro rfl; simp at hJ`. Establish `hI0 : I ≠ ⊥` using `by rintro rfl; simp at hJ`. Establish `hne : ¬ J' ≤ I * J'`.

Introduce `h`. Establish `h1 : I * J' ∣ 1 * J'` using `by rw [one_mul]; exact Ideal.dvd_iff_le.2 h`. Rewrite `h1` using `[mul_dvd_mul_iff_right hJ', Ideal.one_eq_top]`. Conclude with `hI.ne_top (eq_top_iff.2 (Ideal.dvd_iff_le.1 h1))`. Take `⟨c, hc, hcn⟩` from `Set.not_subset.1 hne`.

Use `⟨c, fun a ha => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_comm c a]`. Conclude with `Ideal.mul_mem_mul ha hc`. Establish `hLJ' : Ideal.span {c} ⊔ I * J' ≤ J'` using `sup_le (by rw [Ideal.span_le]; simpa using hc) (Ideal.mul_le_inf.trans inf_le_right)`. Take `⟨L', hL'⟩` from `Ideal.dvd_iff_le.2 hLJ'`.

Establish `hIL' : I ≤ L'`. Establish `h2 : J' * L' ∣ J' * I`. Rewrite using `[← hL', mul_comm J' I]`. Conclude with `Ideal.dvd_iff_le.2 le_sup_right`. Conclude with `Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left hJ').1 h2)`.

Distinguish the cases in `htop : L' = ⊤`. Rewrite `hL'` using `[htop, Ideal.mul_top]`. Establish `hxJ' : x ∈ J'`. Establish `h3 : Ideal.span {x} * I ≤ J' * I`. Rewrite using `[Ideal.span_singleton_mul_le_iff]`.

Introduce `z hz`. Rewrite using `[mul_comm x z, mul_comm J' I]`. Conclude with `hx z hz`. Use `(mul_dvd_mul_iff_right hI0).1 (Ideal.dvd_iff_le.2 h3)` as an intermediate fact. Conclude with `Ideal.dvd_iff_le.1 this (Ideal.mem_span_singleton_self x)`.

Rewrite `hxJ'` using `[← hL', Ideal.mem_span_singleton_sup]`. Take `⟨r, b, hb, hrb⟩` from `hxJ'`. Conclude with `⟨r, by rw [← hrb]; simpa using hb⟩`. Establish `hEq : L' = I` using `(hI.eq_of_le htop hIL').symm`. Rewrite `hL'` using `[hEq, mul_comm]`.

Conclude with `(hcn (by rw [mul_comm I J', ← hL']; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self c))).elim`. Establish `hsup : I ⊔ J = ⊤` using `hI.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hle (h ▸ le_sup_right))`. Use `⟨0, fun a _ => by simp, fun x hx => ⟨0, ?_⟩⟩` and prove the remaining obligations. Take `⟨u, hu, v, hv, huv⟩` from `Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)`. Establish `: x = u * x + x * v` using `by rw [mul_comm u, ← mul_add, huv, mul_one]`.

Rewrite using `[zero_mul, sub_zero, this]`. Conclude with `J.add_mem (hx u hu) (J.mul_mem_left x hv)`.
-/
theorem exists_colon_gen (I J : Ideal R) (hI : I.IsMaximal) (hJ : J ≠ ⊥) :
    ∃ c : R, (∀ a ∈ I, c * a ∈ J) ∧ ∀ x : R, (∀ a ∈ I, a * x ∈ J) → ∃ r : R, x - r * c ∈ J := by
  by_cases hle : J ≤ I
  · obtain ⟨J', rfl⟩ := Ideal.dvd_iff_le.2 hle
    have hJ' : J' ≠ ⊥ := by rintro rfl; simp at hJ
    have hI0 : I ≠ ⊥ := by rintro rfl; simp at hJ
    have hne : ¬ J' ≤ I * J' := by
      intro h
      have h1 : I * J' ∣ 1 * J' := by rw [one_mul]; exact Ideal.dvd_iff_le.2 h
      rw [mul_dvd_mul_iff_right hJ', Ideal.one_eq_top] at h1
      exact hI.ne_top (eq_top_iff.2 (Ideal.dvd_iff_le.1 h1))
    obtain ⟨c, hc, hcn⟩ := Set.not_subset.1 hne
    refine ⟨c, fun a ha => ?_, fun x hx => ?_⟩
    · rw [mul_comm c a]; exact Ideal.mul_mem_mul ha hc
    · have hLJ' : Ideal.span {c} ⊔ I * J' ≤ J' :=
        sup_le (by rw [Ideal.span_le]; simpa using hc) (Ideal.mul_le_inf.trans inf_le_right)
      obtain ⟨L', hL'⟩ := Ideal.dvd_iff_le.2 hLJ'
      have hIL' : I ≤ L' := by
        have h2 : J' * L' ∣ J' * I := by
          rw [← hL', mul_comm J' I]; exact Ideal.dvd_iff_le.2 le_sup_right
        exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left hJ').1 h2)
      by_cases htop : L' = ⊤
      · rw [htop, Ideal.mul_top] at hL'
        have hxJ' : x ∈ J' := by
          have h3 : Ideal.span {x} * I ≤ J' * I := by
            rw [Ideal.span_singleton_mul_le_iff]
            intro z hz
            rw [mul_comm x z, mul_comm J' I]; exact hx z hz
          have := (mul_dvd_mul_iff_right hI0).1 (Ideal.dvd_iff_le.2 h3)
          exact Ideal.dvd_iff_le.1 this (Ideal.mem_span_singleton_self x)
        rw [← hL', Ideal.mem_span_singleton_sup] at hxJ'
        obtain ⟨r, b, hb, hrb⟩ := hxJ'
        exact ⟨r, by rw [← hrb]; simpa using hb⟩
      · have hEq : L' = I := (hI.eq_of_le htop hIL').symm
        rw [hEq, mul_comm] at hL'
        exact (hcn (by rw [mul_comm I J', ← hL']; exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self c))).elim
  · have hsup : I ⊔ J = ⊤ :=
      hI.1.2 _ (lt_of_le_of_ne le_sup_left fun h => hle (h ▸ le_sup_right))
    refine ⟨0, fun a _ => by simp, fun x hx => ⟨0, ?_⟩⟩
    obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)
    have : x = u * x + x * v := by rw [mul_comm u, ← mul_add, huv, mul_one]
    rw [zero_mul, sub_zero, this]
    exact J.add_mem (hx u hu) (J.mul_mem_left x hv)

variable {M : Type} [AddCommGroup M] [Module R M]

omit [IsDedekindDomain R] in
/- English proof (translation)
Conclude with `Submodule.smul_induction_on hz (fun a ha n _ => by`. Rewrite using `[map_smul, smul_eq_mul]`. Conclude with `J.mul_mem_right _ ha)`. Use the proof step `(fun x y hx hy => by rw [map_add]; exact J.add_mem hx hy)`.
-/
theorem map_mem_of_mem_smul_top {S : Type} [CommRing S] {N : Type} [AddCommGroup N] [Module S N]
    (J : Ideal S) (φ : N →ₗ[S] S) {z : N} (hz : z ∈ J • (⊤ : Submodule S N)) : φ z ∈ J := by
  exact Submodule.smul_induction_on hz (fun a ha n _ => by
      rw [map_smul, smul_eq_mul]; exact J.mul_mem_right _ ha)
    (fun x y hx hy => by rw [map_add]; exact J.add_mem hx hy)

omit [IsDedekindDomain R] in
/- English proof (translation)
Take `⟨m0, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Take `⟨n, g, f, -, -, hfg⟩` from `Module.Finite.exists_comp_eq_id_of_projective R M`. Establish `hcoord : ∀ j, ∃ r : R, f m0 j - r * c ∈ J`. Introduce `j`. Use `hc _ fun a ha => ?_` and prove the remaining obligations.

Establish `h1 : a • m0 ∈ J • (⊤ : Submodule R M)`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]`. Conclude with `hy a ha`. Establish `h2` using `map_mem_of_mem_smul_top J ((LinearMap.proj j) ∘ₗ f) h1`. Simplify using `using h2`.

Use `choose r hr using hcoord`. Use `⟨g r, (Submodule.Quotient.eq _).2 ?_⟩` and prove the remaining obligations. Establish `hm0 : m0 = g (f m0)`. Use `congrArg (fun φ => φ m0) hfg` as an intermediate fact. Simplify using `using this.symm`.

Establish `hdec : f m0 - c • r = ∑ j, (f m0 j - r j * c) • Pi.single j (1 : R)`. Use extensionality with `i`. Simplify using `[Finset.sum_apply, Pi.single_apply, mul_comm]`. Establish `: c • g r - m0 = -(g (f m0 - c • r))`. Rewrite using `[map_sub, map_smul, ← hm0]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Use `Submodule.neg_mem _ ?_` and prove the remaining obligations. Rewrite using `[hdec, map_sum]`. Conclude with `Submodule.sum_mem _ fun j _ => by`.

Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem_smul (hr j) trivial`.
-/
theorem mem_range_of_torsion [Module.Finite R M] [Module.Projective R M] (I J : Ideal R) (c : R)
    (hc : ∀ x : R, (∀ a ∈ I, a * x ∈ J) → ∃ r : R, x - r * c ∈ J)
    (y : M ⧸ J • (⊤ : Submodule R M)) (hy : ∀ a ∈ I, a • y = 0) :
    ∃ m : M, Submodule.Quotient.mk (c • m) = y := by
  obtain ⟨m0, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨n, g, f, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R M
  have hcoord : ∀ j, ∃ r : R, f m0 j - r * c ∈ J := by
    intro j
    refine hc _ fun a ha => ?_
    have h1 : a • m0 ∈ J • (⊤ : Submodule R M) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact hy a ha
    have h2 := map_mem_of_mem_smul_top J ((LinearMap.proj j) ∘ₗ f) h1
    simpa using h2
  choose r hr using hcoord
  refine ⟨g r, (Submodule.Quotient.eq _).2 ?_⟩
  have hm0 : m0 = g (f m0) := by
    have := congrArg (fun φ => φ m0) hfg; simpa using this.symm
  have hdec : f m0 - c • r = ∑ j, (f m0 j - r j * c) • Pi.single j (1 : R) := by
    ext i; simp [Finset.sum_apply, Pi.single_apply, mul_comm]
  have : c • g r - m0 = -(g (f m0 - c • r)) := by
    rw [map_sub, map_smul, ← hm0]; abel
  rw [this]
  refine Submodule.neg_mem _ ?_
  rw [hdec, map_sum]
  exact Submodule.sum_mem _ fun j _ => by
    rw [map_smul]; exact Submodule.smul_mem_smul (hr j) trivial

/- English proof (translation)
Set `ek : (R ⧸ I) ≃ₐ[R] I.ResidueField` to `AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I) I.ResidueField) I.bijective_algebraMap_quotient_residueField`. Set `e : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] I.ResidueField ⊗[R] M` to `(TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ TensorProduct.congr ek.toLinearEquiv (LinearEquiv.refl R M)`. Use `haveI : Finite I.ResidueField := Finite.of_equiv _ ek.toEquiv`. Use `haveI : Finite (I.ResidueField ⊗[R] M) := Module.finite_of_finite I.ResidueField`. Establish `hr : Module.finrank I.ResidueField (I.ResidueField ⊗[R] M) = Module.finrank R M` using `Ideal.finrank_fiber_eq_finrank I`.

Use `⟨Finite.of_equiv _ e.toEquiv.symm, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := I.ResidueField), hr, Nat.card_congr ek.toEquiv]`.
-/
theorem card_quot_smul_top [Module.Finite R M] [Module.Projective R M] (I : Ideal R) [I.IsMaximal]
    [Finite (R ⧸ I)] : Finite (M ⧸ I • (⊤ : Submodule R M)) ∧
      Nat.card (M ⧸ I • (⊤ : Submodule R M)) = Nat.card (R ⧸ I) ^ Module.finrank R M := by
  let ek : (R ⧸ I) ≃ₐ[R] I.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ I) I.ResidueField)
      I.bijective_algebraMap_quotient_residueField
  let e : (M ⧸ I • (⊤ : Submodule R M)) ≃ₗ[R] I.ResidueField ⊗[R] M :=
    (TensorProduct.quotTensorEquivQuotSMul M I).symm ≪≫ₗ
      TensorProduct.congr ek.toLinearEquiv (LinearEquiv.refl R M)
  haveI : Finite I.ResidueField := Finite.of_equiv _ ek.toEquiv
  haveI : Finite (I.ResidueField ⊗[R] M) := Module.finite_of_finite I.ResidueField
  have hr : Module.finrank I.ResidueField (I.ResidueField ⊗[R] M) = Module.finrank R M :=
    Ideal.finrank_fiber_eq_finrank I
  refine ⟨Finite.of_equiv _ e.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e.toEquiv, Module.natCard_eq_pow_finrank (K := I.ResidueField), hr,
    Nat.card_congr ek.toEquiv]

/- English proof (translation)
Introduce `R _ _ M _ _ _ _ I J hI hfin hJ`. Take `⟨c, hcI, hc⟩` from `exists_colon_gen I J hI hJ`. Set `f : M →ₗ[R] M ⧸ J • (⊤ : Submodule R M)` to `(J • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.lsmul R M c)`. Establish `hfI : I • (⊤ : Submodule R M) ≤ LinearMap.ker f`. Rewrite using `[Submodule.smul_le]`.

Introduce `a ha m _`. Rewrite using `[LinearMap.mem_ker]`. Simplify using `only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_smul]`. Conclude with `Submodule.smul_mem_smul (hcI a ha) trivial`. Set `g` to `(I • (⊤ : Submodule R M)).liftQ f hfI`.

Establish `hgT : ∀ z, ∀ a ∈ I, a • g z = 0`. Introduce `z a ha`. Take `⟨m, rfl⟩` from `Submodule.Quotient.mk_surjective _ z`. Simplify using `only [g, Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_smul]`. Rewrite using `[mul_comm]`.

Conclude with `Submodule.smul_mem_smul (hcI a ha) trivial`. Set `h : (M ⧸ I • (⊤ : Submodule R M)) → {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0}` to `fun z => ⟨g z, hgT z⟩`. Establish `hsurj : Function.Surjective h`. Introduce and unpack `⟨y, hy⟩`. Take `⟨m, hm⟩` from `mem_range_of_torsion I J c hc y hy`.

Conclude with `⟨Submodule.Quotient.mk m, Subtype.ext (by simpa [h, g, f] using hm)⟩`. Take `⟨hQ, hcard⟩` from `card_quot_smul_top (M := M) I`. Conclude with `⟨Finite.of_surjective h hsurj, (Nat.card_le_card_of_surjective h hsurj).trans hcard.le⟩`.
-/
theorem torsion_card : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M]
    [Module R M] [Module.Finite R M] [Module.Projective R M] (I J : Ideal R), I.IsMaximal →
    Finite (R ⧸ I) → J ≠ ⊥ → Finite {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ∧
      Nat.card {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} ≤
        Nat.card (R ⧸ I) ^ Module.finrank R M := by
  intro R _ _ M _ _ _ _ I J hI hfin hJ
  obtain ⟨c, hcI, hc⟩ := exists_colon_gen I J hI hJ
  let f : M →ₗ[R] M ⧸ J • (⊤ : Submodule R M) :=
    (J • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.lsmul R M c)
  have hfI : I • (⊤ : Submodule R M) ≤ LinearMap.ker f := by
    rw [Submodule.smul_le]
    intro a ha m _
    rw [LinearMap.mem_ker]
    simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearMap.lsmul_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, smul_smul]
    exact Submodule.smul_mem_smul (hcI a ha) trivial
  let g := (I • (⊤ : Submodule R M)).liftQ f hfI
  have hgT : ∀ z, ∀ a ∈ I, a • g z = 0 := by
    intro z a ha
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    simp only [g, Submodule.liftQ_apply, f, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.lsmul_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, smul_smul]
    rw [mul_comm]
    exact Submodule.smul_mem_smul (hcI a ha) trivial
  let h : (M ⧸ I • (⊤ : Submodule R M)) →
      {y : M ⧸ J • (⊤ : Submodule R M) // ∀ a ∈ I, a • y = 0} := fun z => ⟨g z, hgT z⟩
  have hsurj : Function.Surjective h := by
    rintro ⟨y, hy⟩
    obtain ⟨m, hm⟩ := mem_range_of_torsion I J c hc y hy
    exact ⟨Submodule.Quotient.mk m, Subtype.ext (by simpa [h, g, f] using hm)⟩
  obtain ⟨hQ, hcard⟩ := card_quot_smul_top (M := M) I
  exact ⟨Finite.of_surjective h hsurj, (Nat.card_le_card_of_surjective h hsurj).trans hcard.le⟩

end GlobalTheory.TorsionCount

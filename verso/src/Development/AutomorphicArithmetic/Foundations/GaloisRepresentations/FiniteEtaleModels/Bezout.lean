import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit

set_option autoImplicit false

namespace UpperTheory.Gal.FiniteEtaleModels.O

section Form

variable {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)

/- English proof (translation)
Establish `h` using `alt (x + y)`. Simplify using `only [map_add, LinearMap.add_apply, alt x, alt y, zero_add, add_zero] at h`. Conclude with `eq_neg_of_add_eq_zero_right h`.
-/
private lemma skew (alt : ∀ x, B x x = 0) (x y : M) : B x y = - B y x := by
  have h := alt (x + y)
  simp only [map_add, LinearMap.add_apply, alt x, alt y, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

/- English proof (translation)
The claim follows from `Nat.isCoprime_iff_coprime.2 hc`.
-/
private lemma bezout {e n : ℕ} (hc : e.Coprime n) : ∃ a b : ℤ, a * e + b * n = 1 :=
  Nat.isCoprime_iff_coprime.2 hc

/- English proof (translation)
Take `⟨a, b, hab⟩` from `bezout hc`. Set `f : M →ₗ[ℤ] ℤ` to `{ toFun := fun y => B x y / n map_add' := fun y y' => by`. Simplify using `only [map_add]`. Conclude with `Int.add_ediv_of_dvd_right (h y')`. Use the proof step `map_smul' := fun c y => by`.

Simplify using `only [map_smul, smul_eq_mul, RingHom.id_apply]`. Conclude with `Int.mul_ediv_assoc c (h y) }`. Establish `hf : ∀ y, (n : ℤ) * f y = B x y` using `fun y => Int.mul_ediv_cancel' (h y)`. Take `⟨w, hw⟩` from `perf f`. Establish `key : n • w = e • x`.

Apply `nd` to reduce the goal to its premises. Use extensionality with `y`. Simplify using `only [map_nsmul, LinearMap.smul_apply, hw, nsmul_eq_mul, ← hf]`. Expand and normalize the polynomial expressions, which then agree. Establish `key' : (e : ℤ) • x = (n : ℤ) • w`.

Rewrite using `[Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, key]`. Use `⟨a • w + b • x, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[key', ← Nat.cast_smul_eq_nsmul ℤ n, smul_add, smul_comm a, smul_comm b]`.
-/
private lemma first {n e : ℕ} (hn : 0 < n) (hc : e.Coprime n) (nd : Function.Injective B)
    (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (x : M) (h : ∀ y, (n : ℤ) ∣ B x y) :
    ∃ z, x = n • z := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let f : M →ₗ[ℤ] ℤ :=
    { toFun := fun y => B x y / n
      map_add' := fun y y' => by
        simp only [map_add]
        exact Int.add_ediv_of_dvd_right (h y')
      map_smul' := fun c y => by
        simp only [map_smul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (h y) }
  have hf : ∀ y, (n : ℤ) * f y = B x y := fun y => Int.mul_ediv_cancel' (h y)
  obtain ⟨w, hw⟩ := perf f
  have key : n • w = e • x := by
    apply nd
    ext y
    simp only [map_nsmul, LinearMap.smul_apply, hw, nsmul_eq_mul, ← hf]
    ring
  have key' : (e : ℤ) • x = (n : ℤ) • w := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, key]
  refine ⟨a • w + b • x, ?_⟩
  calc x = ((a * e + b * n : ℤ)) • x := by rw [hab, one_smul]
    _ = a • ((e : ℤ) • x) + b • ((n : ℤ) • x) := by rw [add_smul, mul_smul, mul_smul]
    _ = n • (a • w + b • x) := by
      rw [key', ← Nat.cast_smul_eq_nsmul ℤ n, smul_add, smul_comm a, smul_comm b]

/- English proof (translation)
Take `⟨a, b, hab⟩` from `bezout hc`. Set `F : M → M →ₗ[ℤ] ℤ` to `fun y => (B.flip y) ∘ₗ h.toIntLinearMap`. Establish `hF : ∀ y x, F y x = B (h x) y` using `fun y x => rfl`. Use `choose w hw using fun y => perf (F y)`. Establish `wadd : ∀ y y', w (y + y') = w y + w y'`.

Introduce `y y'`. Apply `nd` to reduce the goal to its premises. Use extensionality with `x`. Simplify using `only [map_add, LinearMap.add_apply, hw, LinearMap.smul_apply, hF, smul_add]`. Set `k : M →+ M` to `AddMonoidHom.mk' (fun y => -(a • w y)) (by`.

Introduce `y y'`. Simplify using `only [wadd, smul_add, neg_add])`. Use `⟨k, fun x y => ?_⟩` and prove the remaining obligations. Establish `h1 : B x (k y) = a * (e * B (h x) y)`. Simplify using `only [k, AddMonoidHom.mk'_apply, map_neg, map_zsmul, smul_eq_mul, skew B alt x (w y), hw, LinearMap.smul_apply, hF, nsmul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1]`. Conclude with `⟨b * B (h x) y, by linear_combination (-(B (h x) y)) * hab⟩`.
-/
private lemma second {n e : ℕ} (hc : e.Coprime n) (nd : Function.Injective B)
    (alt : ∀ x, B x x = 0) (perf : ∀ f : M →ₗ[ℤ] ℤ, ∃ x, B x = e • f) (h : M →+ M) :
    ∃ k : M →+ M, ∀ x y, (n : ℤ) ∣ B (h x) y - B x (k y) := by
  obtain ⟨a, b, hab⟩ := bezout hc
  let F : M → M →ₗ[ℤ] ℤ := fun y => (B.flip y) ∘ₗ h.toIntLinearMap
  have hF : ∀ y x, F y x = B (h x) y := fun y x => rfl
  choose w hw using fun y => perf (F y)
  have wadd : ∀ y y', w (y + y') = w y + w y' := by
    intro y y'
    apply nd
    ext x
    simp only [map_add, LinearMap.add_apply, hw, LinearMap.smul_apply, hF, smul_add]
  let k : M →+ M := AddMonoidHom.mk' (fun y => -(a • w y)) (by
    intro y y'
    simp only [wadd, smul_add, neg_add])
  refine ⟨k, fun x y => ?_⟩
  have h1 : B x (k y) = a * (e * B (h x) y) := by
    simp only [k, AddMonoidHom.mk'_apply, map_neg, map_zsmul, smul_eq_mul, skew B alt x (w y), hw,
      LinearMap.smul_apply, hF, nsmul_eq_mul]
    ring
  rw [h1]
  exact ⟨b * B (h x) y, by linear_combination (-(B (h x) y)) * hab⟩

/- English proof (translation)
Set `N : AddSubgroup M` to `(nsmulAddMonoidHom n).range`. Establish `memN : ∀ y, y ∈ N ↔ ∃ z, n • z = y` using `fun y => by`. Simplify using `[N, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]`. Establish `hle : N ≤ N.comap g`. Introduce `y hy`.

Take `⟨z, rfl⟩` from `(memN y).1 hy`. Conclude with `(memN _).2 ⟨g z, (map_nsmul g n z).symm⟩`. Set `G` to `QuotientAddGroup.map N N g hle`. Use `haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance`. Use `haveI : Finite (M ⧸ N) := by`.

Apply `AddCommGroup.finite_of_fg_torsion` to reduce the goal to its premises. Introduce `u`. Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective u`. Rewrite using `[isOfFinAddOrder_iff_nsmul_eq_zero]`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations.

Rewrite using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Conclude with `(memN _).2 ⟨y, rfl⟩`. Establish `ginj : Function.Injective G`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `u hu`.

Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective u`. Rewrite `hu` using `[QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff]`. Take `⟨z, hz⟩` from `(memN _).1 hu`. Take `⟨w, hw⟩` from `inj y z hz.symm`. Rewrite using `[QuotientAddGroup.eq_zero_iff]`.

Conclude with `(memN _).2 ⟨w, hw.symm⟩`. Take `⟨u, hu⟩` from `Finite.injective_iff_surjective.1 ginj (QuotientAddGroup.mk x)`. Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective u`. Rewrite `hu` using `[QuotientAddGroup.map_mk, QuotientAddGroup.eq]`. Take `⟨z, hz⟩` from `(memN _).1 hu`.

Conclude with `⟨y, -z, by rw [smul_neg, hz]; abel⟩`.
-/
private lemma third {n : ℕ} (hn : 0 < n) [Module.Finite ℤ M] (g : M →+ M)
    (inj : ∀ x z, g x = n • z → ∃ w, x = n • w) (x : M) : ∃ y z, g y = x + n • z := by
  classical
  let N : AddSubgroup M := (nsmulAddMonoidHom n).range
  have memN : ∀ y, y ∈ N ↔ ∃ z, n • z = y := fun y => by
    simp [N, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  have hle : N ≤ N.comap g := by
    intro y hy
    obtain ⟨z, rfl⟩ := (memN y).1 hy
    exact (memN _).2 ⟨g z, (map_nsmul g n z).symm⟩
  let G := QuotientAddGroup.map N N g hle
  haveI : AddGroup.FG M := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : Finite (M ⧸ N) := by
    apply AddCommGroup.finite_of_fg_torsion
    intro u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨n, hn, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨y, rfl⟩
  have ginj : Function.Injective G := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq_zero_iff] at hu
    obtain ⟨z, hz⟩ := (memN _).1 hu
    obtain ⟨w, hw⟩ := inj y z hz.symm
    rw [QuotientAddGroup.eq_zero_iff]
    exact (memN _).2 ⟨w, hw.symm⟩
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.1 ginj (QuotientAddGroup.mk x)
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective u
  rw [QuotientAddGroup.map_mk, QuotientAddGroup.eq] at hu
  obtain ⟨z, hz⟩ := (memN _).1 hu
  exact ⟨y, -z, by rw [smul_neg, hz]; abel⟩

end Form

/- English proof (translation)
Introduce `q _ D e`. Use `haveI := D.finLa`. Take `⟨e', he', perf⟩` from `D.perfP`. Establish `hc : e'.Coprime (q ^ e)` using `Nat.Coprime.pow_right e he'`. Establish `hn : 0 < q ^ e` using `pow_pos (Fact.out : Nat.Prime q).pos e`.

Establish `fst : ∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0`. Introduce `x hx`. Take `⟨z, hz⟩` from `first D.EF hn hc D.nondeg perf x hx`. Conclude with `⟨z, by rw [zero_add]; exact hz⟩`. Use `⟨fst, ?_, ?_⟩` and prove the remaining obligations.

Introduce `h`. Take `⟨k, hk⟩` from `second D.EF hc D.nondeg D.alt perf h.toAddMonoidHom`. Use `⟨k, hk, ?_⟩` and prove the remaining obligations. Introduce `c y`. Take `⟨z, hz⟩` from `fst (k (c • y) - c • k y) (by`.

Introduce `x`. Take `⟨b', hb'⟩ : ∃ b', MulOpposite.unop (D.star b') = c` from `⟨_, D.star_star c⟩`. Establish `e1` using `hk x (c • y)`. Establish `e2` using `hk (b' • x) y`. Establish `a1 : D.EF (h.toAddMonoidHom (b' • x)) y = D.EF (h.toAddMonoidHom x) (c • y)`.

Rewrite using `[LinearMap.toAddMonoidHom_coe, map_smul, D.adj, hb']`. Establish `a2 : D.EF (b' • x) (k y) = D.EF x (c • k y)` using `by rw [D.adj, hb']`. Rewrite `e2` using `[a1, a2]`. Rewrite using `[skew D.EF D.alt, map_sub, dvd_neg]`. Establish `h5` using `dvd_sub e2 e1`.

Rewrite using `[sub_sub_sub_cancel_left] at h5)` and apply the resulting hypothesis. Conclude with `⟨z, by rw [zero_add, sub_eq_iff_eq_add'] at hz; exact hz⟩`. Introduce `g hg`. Establish `ginj : ∀ x z, g x = (q ^ e) • z → ∃ w, x = (q ^ e) • w`. Introduce `x z hz`.

Apply `first D.EF hn hc D.nondeg perf x` to reduce the goal to its premises. Introduce `y`. Establish `h3` using `hg x y`. Rewrite `h3` using `[hz, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]`. Establish `h2 : ((q ^ e : ℕ) : ℤ) ∣ ((q ^ e : ℕ) : ℤ) * D.EF z (g y)` using `dvd_mul_right _ _`.

Establish `h4` using `dvd_sub h2 h3`. Rewrite `h4` using `[sub_sub_cancel]`. Then use the resulting hypothesis. Use `⟨fun x ⟨z, hz⟩ => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨w, hw⟩` from `ginj x z (by rw [hz, zero_add])`. Conclude with `⟨w, by rw [zero_add]; exact hw⟩`.

Take `⟨y, z, hyz⟩` from `third hn g ginj x`. Conclude with `⟨y, z, hyz⟩`.
-/
theorem adj : UpperTheory.Gal.FiniteEtaleModels.O.Adj := by
  intro q _ D e
  haveI := D.finLa
  obtain ⟨e', he', perf⟩ := D.perfP
  have hc : e'.Coprime (q ^ e) := Nat.Coprime.pow_right e he'
  have hn : 0 < q ^ e := pow_pos (Fact.out : Nat.Prime q).pos e
  have fst : ∀ x : D.La, (∀ y, ((q ^ e : ℕ) : ℤ) ∣ D.EF x y) → Cg (q ^ e) x 0 := by
    intro x hx
    obtain ⟨z, hz⟩ := first D.EF hn hc D.nondeg perf x hx
    exact ⟨z, by rw [zero_add]; exact hz⟩
  refine ⟨fst, ?_, ?_⟩
  · intro h
    obtain ⟨k, hk⟩ := second D.EF hc D.nondeg D.alt perf h.toAddMonoidHom
    refine ⟨k, hk, ?_⟩
    intro c y
    obtain ⟨z, hz⟩ := fst (k (c • y) - c • k y) (by
      intro x
      obtain ⟨b', hb'⟩ : ∃ b', MulOpposite.unop (D.star b') = c := ⟨_, D.star_star c⟩
      have e1 := hk x (c • y)
      have e2 := hk (b' • x) y
      have a1 : D.EF (h.toAddMonoidHom (b' • x)) y = D.EF (h.toAddMonoidHom x) (c • y) := by
        rw [LinearMap.toAddMonoidHom_coe, map_smul, D.adj, hb']
      have a2 : D.EF (b' • x) (k y) = D.EF x (c • k y) := by rw [D.adj, hb']
      rw [a1, a2] at e2
      rw [skew D.EF D.alt, map_sub, dvd_neg]
      have h5 := dvd_sub e2 e1
      rwa [sub_sub_sub_cancel_left] at h5)
    exact ⟨z, by rw [zero_add, sub_eq_iff_eq_add'] at hz; exact hz⟩
  · intro g hg
    have ginj : ∀ x z, g x = (q ^ e) • z → ∃ w, x = (q ^ e) • w := by
      intro x z hz
      apply first D.EF hn hc D.nondeg perf x
      intro y
      have h3 := hg x y
      rw [hz, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h3
      have h2 : ((q ^ e : ℕ) : ℤ) ∣ ((q ^ e : ℕ) : ℤ) * D.EF z (g y) := dvd_mul_right _ _
      have h4 := dvd_sub h2 h3
      rwa [sub_sub_cancel] at h4
    refine ⟨fun x ⟨z, hz⟩ => ?_, fun x => ?_⟩
    · obtain ⟨w, hw⟩ := ginj x z (by rw [hz, zero_add])
      exact ⟨w, by rw [zero_add]; exact hw⟩
    · obtain ⟨y, z, hyz⟩ := third hn g ginj x
      exact ⟨y, z, hyz⟩

end UpperTheory.Gal.FiniteEtaleModels.O

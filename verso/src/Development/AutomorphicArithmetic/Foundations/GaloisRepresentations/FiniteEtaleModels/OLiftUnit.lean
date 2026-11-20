import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LiftUnit

set_option autoImplicit false

namespace UpperTheory.Gal.FiniteEtaleModels.O.LU

/- English proof (translation)
Establish `hfin` using `Ideal.finite_factors (R := A) hu`. Set `S` to `hfin.toFinset.filter (fun v => ¬ 𝔞 ≤ v.asIdeal)`. Establish `hc : IsCoprime 𝔞 (∏ v ∈ S, v.asIdeal)`. Apply `IsCoprime.prod_right` to reduce the goal to its premises. Introduce `v hv`.

Establish `hm : v.asIdeal.IsMaximal` using `v.isMaximal`. Rewrite using `[Ideal.isCoprime_iff_sup_eq]`. Conclude with `hm.out.2 _ (right_lt_sup.2 (Finset.mem_filter.1 hv).2)`. Take `⟨s, hs, t, ht, hst⟩` from `Ideal.isCoprime_iff_exists.1 hc`. Use `⟨s, t, hs, hst, fun 𝔪 hm hum ha => ?_⟩` and prove the remaining obligations.

Establish `hne : 𝔪 ≠ ⊥` using `fun h => hu (le_bot_iff.1 (h ▸ hum))`. Set `v : IsDedekindDomain.HeightOneSpectrum A` to `⟨𝔪, hm.isPrime, hne⟩`. Establish `hv : v ∈ S`. Use `Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, ha⟩` and prove the remaining obligations. Conclude with `Ideal.dvd_iff_le.2 hum`.

Conclude with `Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun v : IsDedekindDomain.HeightOneSpectrum A => v.asIdeal) hv) ht`.
-/
private theorem exists_sep {A : Type} [CommRing A] [IsDedekindDomain A] (u 𝔞 : Ideal A) (hu : u ≠ ⊥) :
    ∃ s t : A, s ∈ 𝔞 ∧ s + t = 1 ∧ ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 → ¬ 𝔞 ≤ 𝔪 → t ∈ 𝔪 := by
  classical
  have hfin := Ideal.finite_factors (R := A) hu
  let S := hfin.toFinset.filter (fun v => ¬ 𝔞 ≤ v.asIdeal)
  have hc : IsCoprime 𝔞 (∏ v ∈ S, v.asIdeal) := by
    apply IsCoprime.prod_right
    intro v hv
    have hm : v.asIdeal.IsMaximal := v.isMaximal
    rw [Ideal.isCoprime_iff_sup_eq]
    exact hm.out.2 _ (right_lt_sup.2 (Finset.mem_filter.1 hv).2)
  obtain ⟨s, hs, t, ht, hst⟩ := Ideal.isCoprime_iff_exists.1 hc
  refine ⟨s, t, hs, hst, fun 𝔪 hm hum ha => ?_⟩
  have hne : 𝔪 ≠ ⊥ := fun h => hu (le_bot_iff.1 (h ▸ hum))
  let v : IsDedekindDomain.HeightOneSpectrum A := ⟨𝔪, hm.isPrime, hne⟩
  have hv : v ∈ S := by
    refine Finset.mem_filter.2 ⟨hfin.mem_toFinset.2 ?_, ha⟩
    exact Ideal.dvd_iff_le.2 hum
  exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun v : IsDedekindDomain.HeightOneSpectrum A => v.asIdeal) hv) ht

/- English proof (translation)
Use `set R := LinearMap.range g with hR`. Set `I : Ideal A` to `Module.annihilator A (M ⧸ R)`. Establish `hIu : I ⊔ u ^ e = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨𝔪, hm, hle⟩` from `Ideal.exists_le_maximal _ hne`.

Establish `hum : u ≤ 𝔪` using `hm.isPrime.le_of_pow_le (le_sup_right.trans hle)`. Establish `hQ : (⊤ : Submodule A (M ⧸ R)) ≤ 𝔪 • ⊤`. Introduce `y _`. Take `⟨x, rfl⟩` from `R.mkQ_surjective y`. Establish `hx : x ∈ R ⊔ (𝔪 • ⊤ : Submodule A M)` using `by rw [h 𝔪 hm hum]; trivial`.

Take `⟨r, hr, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Establish `h1 : R.mkQ (r + z) = R.mkQ z`. Rewrite using `[map_add, show R.mkQ r = 0 from (Submodule.Quotient.mk_eq_zero R).2 hr, zero_add]`. Rewrite using `[h1]`. Establish `h2` using `Submodule.mem_map_of_mem (f := R.mkQ) hz`.

Rewrite `h2` using `[Submodule.map_smul'']`. Simplify using `using h2`. Take `⟨r, hr1, hr⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 ⊤ Module.Finite.fg_top hQ`. Establish `hrI : r ∈ I` using `Module.mem_annihilator.2 fun y => hr y trivial`. Establish `hrm : r ∈ 𝔪` using `hle (Ideal.mem_sup_left hrI)`.

Conclude with `hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hrm hr1))`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨a, ha, b, hb, hab⟩` from `Submodule.mem_sup.1 (hIu ▸ (Submodule.mem_top : (1 : A) ∈ ⊤))`. Establish `h1 : a • x ∈ R`.

Establish `: a • R.mkQ x = 0` using `Module.mem_annihilator.1 ha _`. Rewrite `this` using `[← map_smul]`. Conclude with `(Submodule.Quotient.mk_eq_zero R).1 this`. Establish `h2 : b • x ∈ (u ^ e • ⊤ : Submodule A M)` using `Submodule.smul_mem_smul hb trivial`. Establish `h3 : x = a • x + b • x` using `by rw [← add_smul, hab, one_smul]`.

Rewrite using `[h3]`. Conclude with `Submodule.add_mem_sup h1 h2`.
-/
private theorem sup_range_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    (g : M →ₗ[A] M) (u : Ideal A)
    (h : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 → LinearMap.range g ⊔ (𝔪 • ⊤ : Submodule A M) = ⊤) (e : ℕ) :
    LinearMap.range g ⊔ (u ^ e • ⊤ : Submodule A M) = ⊤ := by
  set R := LinearMap.range g with hR
  let I : Ideal A := Module.annihilator A (M ⧸ R)
  have hIu : I ⊔ u ^ e = ⊤ := by
    by_contra hne
    obtain ⟨𝔪, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    have hum : u ≤ 𝔪 := hm.isPrime.le_of_pow_le (le_sup_right.trans hle)
    have hQ : (⊤ : Submodule A (M ⧸ R)) ≤ 𝔪 • ⊤ := by
      intro y _
      obtain ⟨x, rfl⟩ := R.mkQ_surjective y
      have hx : x ∈ R ⊔ (𝔪 • ⊤ : Submodule A M) := by rw [h 𝔪 hm hum]; trivial
      obtain ⟨r, hr, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
      have h1 : R.mkQ (r + z) = R.mkQ z := by
        rw [map_add, show R.mkQ r = 0 from (Submodule.Quotient.mk_eq_zero R).2 hr, zero_add]
      rw [h1]
      have h2 := Submodule.mem_map_of_mem (f := R.mkQ) hz
      rw [Submodule.map_smul''] at h2
      simpa using h2
    obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul 𝔪 ⊤
      Module.Finite.fg_top hQ
    have hrI : r ∈ I := Module.mem_annihilator.2 fun y => hr y trivial
    have hrm : r ∈ 𝔪 := hle (Ideal.mem_sup_left hrI)
    exact hm.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem hrm hr1))
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hIu ▸ (Submodule.mem_top : (1 : A) ∈ ⊤))
  have h1 : a • x ∈ R := by
    have : a • R.mkQ x = 0 := Module.mem_annihilator.1 ha _
    rw [← map_smul] at this
    exact (Submodule.Quotient.mk_eq_zero R).1 this
  have h2 : b • x ∈ (u ^ e • ⊤ : Submodule A M) := Submodule.smul_mem_smul hb trivial
  have h3 : x = a • x + b • x := by rw [← add_smul, hab, one_smul]
  rw [h3]
  exact Submodule.add_mem_sup h1 h2

/- English proof (translation)
Use `set P : Submodule A M := J • ⊤ with hP`. Establish `hs : Function.Surjective (P.mkQ ∘ₗ g)`. Introduce `y`. Take `⟨x, rfl⟩` from `P.mkQ_surjective y`. Establish `hx : x ∈ LinearMap.range g ⊔ P` using `by rw [h]; trivial`.

Take `⟨r, ⟨a, rfl⟩, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `[(Submodule.Quotient.mk_eq_zero P).2 hz]`. Take `⟨k, hk⟩` from `Module.projective_lifting_property (P.mkQ ∘ₗ g) P.mkQ hs`. Establish `hk' : ∀ x, P.mkQ (g (k x)) = P.mkQ x` using `fun x => LinearMap.congr_fun hk x`.

Establish `hle : P ≤ P.comap g`. Introduce `x hx`. Establish `h1` using `Submodule.mem_map_of_mem (f := g) hx`. Rewrite `h1` using `[hP, Submodule.map_smul'']`. Conclude with `Submodule.smul_mono le_rfl le_top h1`.

Set `gb : (M ⧸ P) →ₗ[A] (M ⧸ P)` to `P.mapQ P g hle`. Establish `hgb : ∀ x, gb (P.mkQ x) = P.mkQ (g x)` using `fun x => rfl`. Establish `hsb : Function.Surjective gb`. Introduce `y`. Take `⟨z, hz⟩` from `hs y`.

Conclude with `⟨P.mkQ z, by rw [hgb]; exact hz⟩`. Establish `hib : Function.Injective gb` using `OrzechProperty.injective_of_surjective_endomorphism gb hsb`. Use `⟨k, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `(Submodule.Quotient.eq P).1 (hk' x)`. Use `(Submodule.Quotient.eq P).1 (hib ?_)` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `gb (P.mkQ _) = gb (P.mkQ _)`. Rewrite using `[hgb, hgb, hk']`.
-/
private theorem exists_inv {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] (g : M →ₗ[A] M) (J : Ideal A)
    (h : LinearMap.range g ⊔ (J • ⊤ : Submodule A M) = ⊤) :
    ∃ k : M →ₗ[A] M, ∀ x, g (k x) - x ∈ (J • ⊤ : Submodule A M) ∧ k (g x) - x ∈ (J • ⊤ : Submodule A M) := by
  set P : Submodule A M := J • ⊤ with hP
  have hs : Function.Surjective (P.mkQ ∘ₗ g) := by
    intro y
    obtain ⟨x, rfl⟩ := P.mkQ_surjective y
    have hx : x ∈ LinearMap.range g ⊔ P := by rw [h]; trivial
    obtain ⟨r, ⟨a, rfl⟩, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨a, ?_⟩
    simp [(Submodule.Quotient.mk_eq_zero P).2 hz]
  obtain ⟨k, hk⟩ := Module.projective_lifting_property (P.mkQ ∘ₗ g) P.mkQ hs
  have hk' : ∀ x, P.mkQ (g (k x)) = P.mkQ x := fun x => LinearMap.congr_fun hk x
  have hle : P ≤ P.comap g := by
    intro x hx
    have h1 := Submodule.mem_map_of_mem (f := g) hx
    rw [hP, Submodule.map_smul''] at h1
    exact Submodule.smul_mono le_rfl le_top h1
  let gb : (M ⧸ P) →ₗ[A] (M ⧸ P) := P.mapQ P g hle
  have hgb : ∀ x, gb (P.mkQ x) = P.mkQ (g x) := fun x => rfl
  have hsb : Function.Surjective gb := by
    intro y
    obtain ⟨z, hz⟩ := hs y
    exact ⟨P.mkQ z, by rw [hgb]; exact hz⟩
  have hib : Function.Injective gb := OrzechProperty.injective_of_surjective_endomorphism gb hsb
  refine ⟨k, fun x => ⟨?_, ?_⟩⟩
  · exact (Submodule.Quotient.eq P).1 (hk' x)
  · refine (Submodule.Quotient.eq P).1 (hib ?_)
    change gb (P.mkQ _) = gb (P.mkQ _)
    rw [hgb, hgb, hk']

end UpperTheory.Gal.FiniteEtaleModels.O.LU

open UpperTheory.Gal.FiniteEtaleModels.O.LU in
/- English proof (translation)
Introduce `A M _ _ _ _ _ _ u 𝔞 hu _`. Use `set N : Submodule A M := 𝔞 • ⊤ with hN`. Introduce `g₀`. Take `⟨g', hg'⟩` from `Module.projective_lifting_property N.mkQ (g₀.toLinearMap ∘ₗ N.mkQ) N.mkQ_surjective`. Take `⟨s, t, hs, hst, ht⟩` from `exists_sep u 𝔞 hu`.

Set `g : M →ₗ[A] M` to `t • g' + s • LinearMap.id`. Establish `hgv : ∀ x, g x = t • g' x + s • x` using `fun x => rfl`. Establish `ht1 : t = 1 - s` using `by rw [← hst]; ring`. Establish `hs1 : s = 1 - t` using `by rw [← hst]; ring`. Establish `hgg' : ∀ x, g x - g' x ∈ N` using `fun x => by`.

Establish `h1 : g x - g' x = s • (x - g' x)`. Rewrite using `[hgv, ht1, sub_smul, one_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem_smul hs trivial`.

Establish `hlift : ∀ x, N.mkQ (g x) = g₀ (N.mkQ x)` using `fun x => by`. Establish `h1 : N.mkQ (g x) = N.mkQ (g' x)` using `(Submodule.Quotient.eq N).2 (hgg' x)`. Rewrite using `[h1]`. Conclude with `LinearMap.congr_fun hg' x`. Establish `hmax : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 → LinearMap.range g ⊔ (𝔪 • ⊤ : Submodule A M) = ⊤`.

Introduce `𝔪 hm hum`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Distinguish the cases in `ha : 𝔞 ≤ 𝔪`. Take `⟨y, hy⟩` from `g₀.surjective (N.mkQ x)`.

Take `⟨y, rfl⟩` from `N.mkQ_surjective y`. Establish `h1 : x - g y ∈ N` using `(Submodule.Quotient.eq N).1 (show N.mkQ x = N.mkQ (g y) by rw [hlift, hy])`. Establish `h2 : x - g y ∈ (𝔪 • ⊤ : Submodule A M)` using `Submodule.smul_mono_left ha h1`. Establish `h3` using `Submodule.add_mem_sup (LinearMap.mem_range_self g y) h2`. Simplify using `using h3`.

Establish `htm` using `ht 𝔪 hm hum ha`. Establish `h1 : x - g x = t • (x - g' x)`. Rewrite using `[hgv, hs1, sub_smul, one_smul, smul_sub]`. Normalize the expressions using the abelian group laws. Establish `h2 : x - g x ∈ (𝔪 • ⊤ : Submodule A M)`.

Rewrite using `[h1]`. Conclude with `Submodule.smul_mem_smul htm trivial`. Establish `h3` using `Submodule.add_mem_sup (LinearMap.mem_range_self g x) h2`. Simplify using `using h3`. Use `choose h hh using fun e => exists_inv g (u ^ e) (sup_range_pow g u hmax e)`.

Conclude with `⟨g, h, hlift, fun e x => hh e x⟩`.
-/
theorem UpperTheory.Gal.FiniteEtaleModels.O.liftUnit :
    UpperTheory.Gal.FiniteEtaleModels.O.LiftUnit := by
  intro A M _ _ _ _ _ _ u 𝔞 hu _
  set N : Submodule A M := 𝔞 • ⊤ with hN
  intro g₀
  obtain ⟨g', hg'⟩ := Module.projective_lifting_property N.mkQ (g₀.toLinearMap ∘ₗ N.mkQ) N.mkQ_surjective
  obtain ⟨s, t, hs, hst, ht⟩ := exists_sep u 𝔞 hu
  let g : M →ₗ[A] M := t • g' + s • LinearMap.id
  have hgv : ∀ x, g x = t • g' x + s • x := fun x => rfl
  have ht1 : t = 1 - s := by rw [← hst]; ring
  have hs1 : s = 1 - t := by rw [← hst]; ring
  have hgg' : ∀ x, g x - g' x ∈ N := fun x => by
    have h1 : g x - g' x = s • (x - g' x) := by
      rw [hgv, ht1, sub_smul, one_smul, smul_sub]; abel
    rw [h1]
    exact Submodule.smul_mem_smul hs trivial
  have hlift : ∀ x, N.mkQ (g x) = g₀ (N.mkQ x) := fun x => by
    have h1 : N.mkQ (g x) = N.mkQ (g' x) := (Submodule.Quotient.eq N).2 (hgg' x)
    rw [h1]
    exact LinearMap.congr_fun hg' x
  have hmax : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → u ≤ 𝔪 →
      LinearMap.range g ⊔ (𝔪 • ⊤ : Submodule A M) = ⊤ := by
    intro 𝔪 hm hum
    rw [eq_top_iff]
    intro x _
    by_cases ha : 𝔞 ≤ 𝔪
    · obtain ⟨y, hy⟩ := g₀.surjective (N.mkQ x)
      obtain ⟨y, rfl⟩ := N.mkQ_surjective y
      have h1 : x - g y ∈ N := (Submodule.Quotient.eq N).1 (show N.mkQ x = N.mkQ (g y) by rw [hlift, hy])
      have h2 : x - g y ∈ (𝔪 • ⊤ : Submodule A M) := Submodule.smul_mono_left ha h1
      have h3 := Submodule.add_mem_sup (LinearMap.mem_range_self g y) h2
      simpa using h3
    · have htm := ht 𝔪 hm hum ha
      have h1 : x - g x = t • (x - g' x) := by
        rw [hgv, hs1, sub_smul, one_smul, smul_sub]; abel
      have h2 : x - g x ∈ (𝔪 • ⊤ : Submodule A M) := by
        rw [h1]
        exact Submodule.smul_mem_smul htm trivial
      have h3 := Submodule.add_mem_sup (LinearMap.mem_range_self g x) h2
      simpa using h3
  choose h hh using fun e => exists_inv g (u ^ e) (sup_range_pow g u hmax e)
  exact ⟨g, h, hlift, fun e x => hh e x⟩

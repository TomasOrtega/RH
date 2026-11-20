import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.RegularUFDLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal Module

universe u

section Cofactor

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] {n : ℕ}

noncomputable def cofactorLinear (bN : Module.Basis (Fin n) R N) :
    M × N →ₗ[R] (M × N) [⋀^Fin n]→ₗ[R] M where
  toFun x := (bN.det.compLinearMap (LinearMap.snd R M N)).smulRight x.1
  map_add' x y := AlternatingMap.ext fun _ ↦ by simp
  map_smul' c x := AlternatingMap.ext fun _ ↦ by simp [smul_smul, mul_comm]

noncomputable def cofactorToLeft (bN : Module.Basis (Fin n) R N) :
    ⋀[R]^(n + 1) (M × N) →ₗ[R] M :=
  exteriorPower.alternatingMapLinearEquiv (AlternatingMap.alternatizeUncurryFin (cofactorLinear bN))

/- English proof (translation)
Simplify using `[cofactorToLeft, cofactorLinear, AlternatingMap.alternatizeUncurryFin_apply, Fin.sum_univ_succ, Module.Basis.det_self]`.
-/
theorem cofactorToLeft_ιMulti_cons (bN : Module.Basis (Fin n) R N) (m : M) :
    cofactorToLeft bN (exteriorPower.ιMulti R (n + 1) (Fin.cons (m, 0) fun i ↦ (0, bN i))) = m := by
  simp [cofactorToLeft, cofactorLinear, AlternatingMap.alternatizeUncurryFin_apply,
    Fin.sum_univ_succ, Module.Basis.det_self]

end Cofactor

/- English proof (translation)
Take `⟨N, _, _, _, _, hfree⟩` from `IsStablyFree.exist_free_prod D P`. Set `n` to `Module.finrank D N`. Set `𝔭 : PrimeSpectrum D` to `⟨⊥, Ideal.bot_prime⟩`. Establish `h1 : rankAtStalk P 𝔭 = 1`. Set `Dp` to `Localization.AtPrime 𝔭.asIdeal`.

Set `pc` to `𝔭.asIdeal.primeCompl`. Set `f` to `Algebra.linearMap D Dp`. Set `g` to `P.toLocalized' Dp pc f`. Establish `htop : P.localized' Dp pc f = ⊤`. Rewrite using `[Ideal.localized'_eq_map]`.

Take `⟨a, ha, ha0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hP`. Conclude with `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha) (IsLocalization.map_units Dp (⟨a, fun h ↦ ha0 h⟩ : pc))`. Set `e` to `((IsLocalizedModule.linearEquiv pc (LocalizedModule.mkLinearMap pc P) g ).extendScalarsOfIsLocalization pc Dp).trans ((LinearEquiv.ofEq _ _ htop).trans (Submodule.topEquiv))`. Express the relevant statement in the definitionally equal form `Module.finrank Dp (LocalizedModule pc P) = 1`. Rewrite using `[e.finrank_eq, Module.finrank_self]`.

Establish `hp : Module.finrank D (P × N) = n + 1`. Establish `heq` using `congr($(rankAtStalk_prod P N) 𝔭)`. Simplify using `only [rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Pi.add_apply, h1] at heq`. Use `grind`. Set `e : D ≃ₗ[D] ⋀[D]^(n + 1) (P × N)` to `(Module.nonempty_linearEquiv_of_finrank_eq_one <| by simp [exteriorPower.finrank_eq, hp]).some`.

Set `bN : Module.Basis (Fin n) D N` to `Module.finBasis D N`. Set `f : D →ₗ[D] P` to `cofactorToLeft bN ∘ₗ e`. Establish `hf : Function.Surjective f` using `fun x ↦ ⟨e.symm (exteriorPower.ιMulti D (n + 1) (Fin.cons (x, 0) fun i ↦ (0, bN i))), by`. Simplify using `[f, cofactorToLeft_ιMulti_cons]⟩`. Use `⟨(f 1 : D), ?_⟩` and prove the remaining obligations.

Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`. Take `⟨r, hr⟩` from `hf ⟨y, hy⟩`. Establish `: y = r * (f 1 : D)`. Rewrite using `[← smul_eq_mul, ← Submodule.coe_smul, ← map_smul, smul_eq_mul, mul_one, hr]`.

Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ (Submodule.mem_span_singleton_self _)`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `(f 1).2`.
-/
theorem isPrincipal_of_isStablyFree {D : Type u} [CommRing D] [IsDomain D] [IsNoetherianRing D]
    (P : Ideal D)
    (hP : P ≠ ⊥) [IsStablyFree D P] : P.IsPrincipal := by
  obtain ⟨N, _, _, _, _, hfree⟩ := IsStablyFree.exist_free_prod D P
  let n := Module.finrank D N

  let 𝔭 : PrimeSpectrum D := ⟨⊥, Ideal.bot_prime⟩
  have h1 : rankAtStalk P 𝔭 = 1 := by
    let Dp := Localization.AtPrime 𝔭.asIdeal
    let pc := 𝔭.asIdeal.primeCompl
    let f := Algebra.linearMap D Dp
    let g := P.toLocalized' Dp pc f
    have htop : P.localized' Dp pc f = ⊤ := by
      rw [Ideal.localized'_eq_map]
      obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
      exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ ha)
        (IsLocalization.map_units Dp (⟨a, fun h ↦ ha0 h⟩ : pc))
    let e := ((IsLocalizedModule.linearEquiv pc (LocalizedModule.mkLinearMap pc P) g
      ).extendScalarsOfIsLocalization pc Dp).trans
      ((LinearEquiv.ofEq _ _ htop).trans (Submodule.topEquiv))
    change Module.finrank Dp (LocalizedModule pc P) = 1
    rw [e.finrank_eq, Module.finrank_self]
  have hp : Module.finrank D (P × N) = n + 1 := by
    have heq := congr($(rankAtStalk_prod P N) 𝔭)
    simp only [rankAtStalk_eq_finrank_of_free, Pi.natCast_apply, Pi.add_apply, h1] at heq
    grind
  let e : D ≃ₗ[D] ⋀[D]^(n + 1) (P × N) :=
    (Module.nonempty_linearEquiv_of_finrank_eq_one <| by simp [exteriorPower.finrank_eq, hp]).some
  let bN : Module.Basis (Fin n) D N := Module.finBasis D N
  let f : D →ₗ[D] P := cofactorToLeft bN ∘ₗ e
  have hf : Function.Surjective f := fun x ↦
    ⟨e.symm (exteriorPower.ιMulti D (n + 1) (Fin.cons (x, 0) fun i ↦ (0, bN i))), by
      simp [f, cofactorToLeft_ιMulti_cons]⟩
  refine ⟨(f 1 : D), ?_⟩
  apply le_antisymm
  · intro y hy
    obtain ⟨r, hr⟩ := hf ⟨y, hy⟩
    have : y = r * (f 1 : D) := by
      rw [← smul_eq_mul, ← Submodule.coe_smul, ← map_smul, smul_eq_mul, mul_one, hr]
    rw [this]
    exact Ideal.mul_mem_left _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact (f 1).2

open CategoryTheory in

/- English proof (translation)
Proceed by induction on `k generalizing M with`. Consider the case `zero`. Rewrite `hM` using `[zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]`. Establish `: Module.Free R M` using `Module.free_of_flat_of_isLocalRing`. Use `Module.free_of_isLocalizedModule (Rₛ := Localization T) T (LocalizedModule.mkLinearMap T M)` as an intermediate fact.

Use `infer_instance`. Consider the case `succ k ih`. Take `⟨n, π, hπ⟩` from `Module.Finite.exists_fin' R M`. Set `K` to `LinearMap.ker π`. Establish `hS` using `LinearMap.shortExact_shortComplexKer hπ`.

Establish `hprojF : Projective (π.shortComplexKer).X₂`. Rewrite using `[← IsProjective.iff_projective]`. Use `infer_instance`. Establish `hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1)` using `(hS.hasProjectiveDimensionLT_X₃_iff k hprojF).mp hM`. Set `A` to `Localization T`.

Set `mkK` to `LocalizedModule.mkLinearMap T K`. Set `mkF` to `LocalizedModule.mkLinearMap T (Fin n → R)`. Set `mkM` to `LocalizedModule.mkLinearMap T M`. Set `φ₁` to `(IsLocalizedModule.map T mkK mkF K.subtype).extendScalarsOfIsLocalization T A`. Set `φ₂` to `(IsLocalizedModule.map T mkF mkM π).extendScalarsOfIsLocalization T A`.

Establish `hex0 : Function.Exact K.subtype π` using `fun y ↦ ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩`. Establish `ex : Function.Exact φ₁ φ₂` using `LocalizedModule.map_exact T K.subtype π hex0`. Establish `inj : Function.Injective φ₁` using `IsLocalizedModule.map_injective T mkK mkF K.subtype K.injective_subtype`. Establish `surj : Function.Surjective φ₂` using `IsLocalizedModule.map_surjective T mkF mkM π hπ`. Take `⟨h, hh⟩` from `Module.projective_lifting_property φ₂ LinearMap.id surj`.

Set `e` to `(Function.Exact.splitSurjectiveEquiv (R := A) (M := LocalizedModule T K) (N := LocalizedModule T (Fin n → R)) (P := LocalizedModule T M) (f := φ₁) (g := φ₂) ex inj ⟨h, hh⟩).1`. Establish `hFfree : Module.Free A (LocalizedModule T (Fin n → R))` using `Module.free_of_isLocalizedModule T mkF`. Establish `: Module.Free A (LocalizedModule T K × LocalizedModule T M)` using `Module.Free.of_equiv e`. Establish `hKproj : Module.Projective A (LocalizedModule T K)` using `Module.Projective.of_split (LinearMap.inl A _ (LocalizedModule T M)) (LinearMap.fst A _ _) (LinearMap.ext fun _ ↦ rfl)`. Establish `hKsf` using `ih K hK hKproj`.

Take `⟨N, _, _, _, _, hNfree⟩` from `IsStablyFree.exist_free_prod A (LocalizedModule T K)`. Establish `: Module.Finite R K` using `inferInstance`. Establish `: Module.Finite A (LocalizedModule T K)` using `inferInstance`. Establish `: Module.Free A (LocalizedModule T M × (LocalizedModule T K × N))`. Conclude with `Module.Free.of_equiv ((LinearEquiv.prodAssoc A (LocalizedModule T M) (LocalizedModule T K) N).symm.trans (((LinearEquiv.prodComm A _ _).trans e.symm).prodCongr (LinearEquiv.refl A N))).symm`.

Conclude with `IsStablyFree.of_free_prod A (LocalizedModule T M) (LocalizedModule T K × N)`.
-/
theorem isStablyFree_localizedModule {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (T : Submonoid R) (k : ℕ) (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : HasProjectiveDimensionLT (ModuleCat.of R M) (k + 1))
    (hproj : Module.Projective (Localization T) (LocalizedModule T M)) :
    IsStablyFree (Localization T) (LocalizedModule T M) := by
  induction k generalizing M with
  | zero =>
    rw [zero_add, ← projective_iff_hasProjectiveDimensionLT_one, ← IsProjective.iff_projective]
      at hM
    have : Module.Free R M := Module.free_of_flat_of_isLocalRing
    have := Module.free_of_isLocalizedModule (Rₛ := Localization T) T
      (LocalizedModule.mkLinearMap T M)
    infer_instance
  | succ k ih =>
    obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
    let K := LinearMap.ker π
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hprojF : Projective (π.shortComplexKer).X₂ := by
      rw [← IsProjective.iff_projective]; infer_instance
    have hK : HasProjectiveDimensionLT (ModuleCat.of R K) (k + 1) :=
      (hS.hasProjectiveDimensionLT_X₃_iff k hprojF).mp hM
    let A := Localization T
    let mkK := LocalizedModule.mkLinearMap T K
    let mkF := LocalizedModule.mkLinearMap T (Fin n → R)
    let mkM := LocalizedModule.mkLinearMap T M
    let φ₁ := (IsLocalizedModule.map T mkK mkF K.subtype).extendScalarsOfIsLocalization T A
    let φ₂ := (IsLocalizedModule.map T mkF mkM π).extendScalarsOfIsLocalization T A
    have hex0 : Function.Exact K.subtype π := fun y ↦
      ⟨fun h ↦ ⟨⟨y, h⟩, rfl⟩, by rintro ⟨k, rfl⟩; exact k.2⟩
    have ex : Function.Exact φ₁ φ₂ := LocalizedModule.map_exact T K.subtype π hex0
    have inj : Function.Injective φ₁ :=
      IsLocalizedModule.map_injective T mkK mkF K.subtype K.injective_subtype
    have surj : Function.Surjective φ₂ := IsLocalizedModule.map_surjective T mkF mkM π hπ
    obtain ⟨h, hh⟩ := Module.projective_lifting_property φ₂ LinearMap.id surj
    let e := (Function.Exact.splitSurjectiveEquiv (R := A) (M := LocalizedModule T K)
      (N := LocalizedModule T (Fin n → R)) (P := LocalizedModule T M) (f := φ₁) (g := φ₂) ex inj
      ⟨h, hh⟩).1
    have hFfree : Module.Free A (LocalizedModule T (Fin n → R)) :=
      Module.free_of_isLocalizedModule T mkF
    have : Module.Free A (LocalizedModule T K × LocalizedModule T M) := Module.Free.of_equiv e
    have hKproj : Module.Projective A (LocalizedModule T K) :=
      Module.Projective.of_split (LinearMap.inl A _ (LocalizedModule T M))
        (LinearMap.fst A _ _) (LinearMap.ext fun _ ↦ rfl)
    have hKsf := ih K hK hKproj
    obtain ⟨N, _, _, _, _, hNfree⟩ := IsStablyFree.exist_free_prod A (LocalizedModule T K)
    have : Module.Finite R K := inferInstance
    have : Module.Finite A (LocalizedModule T K) := inferInstance
    have : Module.Free A (LocalizedModule T M × (LocalizedModule T K × N)) := by
      exact Module.Free.of_equiv ((LinearEquiv.prodAssoc A (LocalizedModule T M)
        (LocalizedModule T K) N).symm.trans
          (((LinearEquiv.prodComm A _ _).trans e.symm).prodCongr (LinearEquiv.refl A N))).symm
    exact IsStablyFree.of_free_prod A (LocalizedModule T M) (LocalizedModule T K × N)

instance (priority := 100) IsRegularLocalRing.toIsDomain {R : Type u} [CommRing R]
    [IsRegularLocalRing R] : IsDomain R :=
  IsRegularLocalRing.isDomain

/- English proof (translation)
Set `A` to `Localization.Away x`. Set `Aq` to `Localization.AtPrime q`. Set `Q'` to `q.comap (algebraMap S A)`. Establish `hQ' : Q'.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `: IsLocalization.AtPrime Aq Q'` using `IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers x) Aq q`.

Use `IsRegularLocalRing.localization_atPrime Q'` as an intermediate fact. Set `e : Aq ≃ₐ[S] Localization.AtPrime Q'` to `IsLocalization.algEquiv Q'.primeCompl _ _`. Establish `hreg : IsRegularLocalRing Aq` using `IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv`. Use `⟨hreg, ?_⟩` and prove the remaining obligations. Establish `hxQ : x ∉ Q'` using `fun h ↦ hQ'.ne_top' (by`.

Establish `hu` using `IsLocalization.Away.algebraMap_isUnit (S := A) x`. Conclude with `(Ideal.comap_eq_top_iff).mpr (q.eq_top_of_isUnit_mem h hu))`. Establish `hlt : Q' < maximalIdeal S` using `lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ'.ne_top) (fun h ↦ hxQ (h ▸ hx))`. Establish `h1 : ((maximalIdeal Aq).spanFinrank : WithBot ℕ∞) = (Q'.height : WithBot ℕ∞)`. Rewrite using `[(isRegularLocalRing_iff Aq).mp hreg, IsLocalization.AtPrime.ringKrullDim_eq_height Q' Aq]`.

Establish `h2 : Q'.height + 1 ≤ (maximalIdeal S).height` using `Ideal.height_add_one_le_of_lt_of_isPrime hlt`. Establish `h3 : ((maximalIdeal S).height : WithBot ℕ∞) = ((maximalIdeal S).spanFinrank : WithBot ℕ∞)`. Rewrite using `[IsLocalRing.maximalIdeal_height_eq_ringKrullDim, (isRegularLocalRing_iff S).mp inferInstance]`. Establish `h1' : Q'.height = ((maximalIdeal Aq).spanFinrank : ℕ∞)` using `by exact_mod_cast h1.symm`. Establish `h3' : (maximalIdeal S).height = ((maximalIdeal S).spanFinrank : ℕ∞)` using `by exact_mod_cast h3`.

Rewrite `h2` using `[h1', h3']`. Establish `: (maximalIdeal Aq).spanFinrank + 1 ≤ (maximalIdeal S).spanFinrank` using `by exact_mod_cast h2`. Express the relevant statement in the definitionally equal form `(maximalIdeal Aq).spanFinrank < _`. Use linear arithmetic over natural numbers and integers.
-/
theorem isRegularLocalRing_localization_away_atPrime {S : Type u} [CommRing S]
    [IsRegularLocalRing S] {x : S} (hx : x ∈ maximalIdeal S)
    (q : Ideal (Localization.Away x)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) ∧
      (maximalIdeal (Localization.AtPrime q)).spanFinrank < (maximalIdeal S).spanFinrank := by
  let A := Localization.Away x
  let Aq := Localization.AtPrime q
  let Q' := q.comap (algebraMap S A)
  have hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
  have : IsLocalization.AtPrime Aq Q' :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (Submonoid.powers x) Aq q
  have := IsRegularLocalRing.localization_atPrime Q'
  let e : Aq ≃ₐ[S] Localization.AtPrime Q' := IsLocalization.algEquiv Q'.primeCompl _ _
  have hreg : IsRegularLocalRing Aq := IsRegularLocalRing.of_ringEquiv e.symm.toRingEquiv
  refine ⟨hreg, ?_⟩
  have hxQ : x ∉ Q' := fun h ↦ hQ'.ne_top' (by
    have hu := IsLocalization.Away.algebraMap_isUnit (S := A) x
    exact (Ideal.comap_eq_top_iff).mpr (q.eq_top_of_isUnit_mem h hu))
  have hlt : Q' < maximalIdeal S :=
    lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hQ'.ne_top) (fun h ↦ hxQ (h ▸ hx))
  have h1 : ((maximalIdeal Aq).spanFinrank : WithBot ℕ∞) = (Q'.height : WithBot ℕ∞) := by
    rw [(isRegularLocalRing_iff Aq).mp hreg, IsLocalization.AtPrime.ringKrullDim_eq_height Q' Aq]
  have h2 : Q'.height + 1 ≤ (maximalIdeal S).height := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  have h3 : ((maximalIdeal S).height : WithBot ℕ∞) = ((maximalIdeal S).spanFinrank : WithBot ℕ∞) := by
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, (isRegularLocalRing_iff S).mp inferInstance]
  have h1' : Q'.height = ((maximalIdeal Aq).spanFinrank : ℕ∞) := by exact_mod_cast h1.symm
  have h3' : (maximalIdeal S).height = ((maximalIdeal S).spanFinrank : ℕ∞) := by exact_mod_cast h3
  rw [h1', h3'] at h2
  have : (maximalIdeal Aq).spanFinrank + 1 ≤ (maximalIdeal S).spanFinrank := by exact_mod_cast h2
  change (maximalIdeal Aq).spanFinrank < _
  omega

/- English proof (translation)
It suffices to establish `H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S], (maximalIdeal S).spanFinrank = n → UniqueFactorizationMonoid S from H _ R rfl`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `S _ _ hn`.

Establish `hd : ringKrullDim S = (n : WithBot ℕ∞)`. Rewrite using `[← hn]`. Conclude with `((isRegularLocalRing_iff S).mp inferInstance).symm`. Establish `hfg : (maximalIdeal S).FG` using `(maximalIdeal S).fg_of_isNoetherianRing`. Distinguish the cases in `h0 : n = 0`.

Apply `UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one` to reduce the goal to its premises. Introduce `p hp hp1`. It suffices to derive a contradiction. Establish `h` using `Ideal.height_le_ringKrullDim_of_ne_top hp.ne_top`. Rewrite `h` using `[hp1, hd, h0]`.

Establish `: (1 : ℕ) ≤ 0` using `by exact_mod_cast h`. Use linear arithmetic over natural numbers and integers. Establish `hjac : maximalIdeal S ≤ jacobson ⊥` using `(IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge`. Establish `hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2`. Introduce `hle`.

Establish `: maximalIdeal S = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg (by simpa [pow_two, smul_eq_mul] using hle) hjac`. Conclude with `h0 (by rw [← hn, this]; simp)`. Take `⟨x, hx, hx2⟩` from `Set.not_subset.mp hsq`. Establish `hx0 : x ≠ 0` using `fun h ↦ hx2 (h ▸ zero_mem _)`. Establish `hne : span {x} ≠ ⊤` using `fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))`.

Establish `: Nontrivial (S ⧸ span {x})` using `Ideal.Quotient.nontrivial_iff.mpr hne`. Establish `: IsLocalRing (S ⧸ span {x})` using `.of_surjective' _ Ideal.Quotient.mk_surjective`. Take `⟨hreg, -⟩` from `isRegularLocalRing_quotient hx hx2`. Establish `hprime : (span {x} : Ideal S).IsPrime` using `(Ideal.Quotient.isDomain_iff_prime _).mp inferInstance`. Establish `hxp : Prime x` using `(Ideal.span_singleton_prime hx0).mp hprime`.

Rewrite using `[UniqueFactorizationMonoid.iff_localizationAway_of_prime hxp]`. Set `A` to `Localization.Away x`. Establish `: IsDomain A` using `Localization.Away.isDomain hx0`. Apply `UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one` to reduce the goal to its premises. Introduce `P hP hP1`.

Establish `hP0 : P ≠ ⊥` using `P.ne_bot_of_height_eq_one hP1`. Establish `: Module.FinitePresentation A P` using `Module.finitePresentation_of_finite A P`. Establish `hPproj : Module.Projective A P`. Apply `Module.projective_of_localization_maximal` to reduce the goal to its premises. Introduce `q hq`.

Take `⟨hregq, hltq⟩` from `isRegularLocalRing_localization_away_atPrime hx q`. Set `Aq` to `Localization.AtPrime q`. Establish `: UniqueFactorizationMonoid Aq` using `ih _ (hn ▸ hltq) Aq rfl`. Establish `hPq : (P.map (algebraMap A Aq)).IsPrincipal`. Distinguish the cases in `hle : P ≤ q`.

Establish `hdisj : Disjoint (q.primeCompl : Set A) (P : Set A)`. Rewrite using `[Set.disjoint_left]`. Introduce `a ha haP`. Conclude with `ha (hle haP)`. Establish `: (P.map (algebraMap A Aq)).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl Aq P hP hdisj`.

Conclude with `UniqueFactorizationMonoid.isPrincipal_of_height_eq_one (by rw [IsLocalization.height_map_of_disjoint q.primeCompl P hdisj, hP1])`. Take `⟨a, haP, haq⟩` from `Set.not_subset.mp hle`. Establish `htop : P.map (algebraMap A Aq) = ⊤` using `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ haP) (IsLocalization.map_units Aq (⟨a, haq⟩ : q.primeCompl))`. Rewrite using `[htop]`. Conclude with `⟨⟨1, Ideal.span_singleton_one.symm⟩⟩`.

Set `f` to `Algebra.linearMap A Aq`. Set `g` to `P.toLocalized' Aq q.primeCompl f`. Set `e` to `((IsLocalizedModule.linearEquiv q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl P) g).extendScalarsOfIsLocalization q.primeCompl Aq).trans (LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map Aq q.primeCompl P))`. Take `⟨⟨c, hc⟩⟩` from `hPq`. Establish `hfree : Module.Free Aq (P.map (algebraMap A Aq))`.

Distinguish the cases in `hc0 : c = 0`. Establish `: Subsingleton (P.map (algebraMap A Aq))`. Rewrite using `[hc, hc0, Submodule.span_singleton_eq_bot.mpr rfl]`. Use `infer_instance`. Use `infer_instance`.

Conclude with `Module.Free.of_equiv ((LinearEquiv.toSpanNonzeroSingleton Aq Aq c hc0).trans (LinearEquiv.ofEq _ _ hc.symm))`. Conclude with `Module.Projective.of_equiv e.symm`. Set `Q` to `P.comap (algebraMap S A)`. Establish `hQpd` using `hasProjectiveDimensionLT_of_isRegularLocalRing hd Q`. Set `T` to `Submonoid.powers x`.

Set `f` to `Algebra.linearMap S A`. Set `gQ` to `Q.toLocalized' A T f`. Establish `hloc : Q.localized' A T f = P`. Rewrite using `[Ideal.localized'_eq_map]`. Conclude with `IsLocalization.map_comap T A P`.

Set `eQ : LocalizedModule T Q ≃ₗ[A] P` to `((IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T Q) gQ ).extendScalarsOfIsLocalization T A).trans (LinearEquiv.ofEq _ _ hloc)`. Establish `hproj' : Module.Projective A (LocalizedModule T Q)` using `Module.Projective.of_equiv eQ.symm`. Establish `hsf` using `isStablyFree_localizedModule T n Q hQpd hproj'`. Establish `: IsStablyFree A P` using `IsStablyFree.equiv eQ`. Conclude with `isPrincipal_of_isStablyFree P hP0`.
-/
theorem IsRegularLocalRing.uniqueFactorizationMonoid (R : Type u) [CommRing R]
    [IsRegularLocalRing R] : UniqueFactorizationMonoid R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → UniqueFactorizationMonoid S from H _ R rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn
  have hd : ringKrullDim S = (n : WithBot ℕ∞) := by
    rw [← hn]; exact ((isRegularLocalRing_iff S).mp inferInstance).symm
  have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
  by_cases h0 : n = 0
  · apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
    intro p hp hp1
    exfalso
    have h := Ideal.height_le_ringKrullDim_of_ne_top hp.ne_top
    rw [hp1, hd, h0] at h
    have : (1 : ℕ) ≤ 0 := by exact_mod_cast h
    omega
  have hjac : maximalIdeal S ≤ jacobson ⊥ :=
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
  have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
    intro hle
    have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
      (by simpa [pow_two, smul_eq_mul] using hle) hjac
    exact h0 (by rw [← hn, this]; simp)
  obtain ⟨x, hx, hx2⟩ := Set.not_subset.mp hsq
  have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ zero_mem _)
  have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
    (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
  have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
  have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
  obtain ⟨hreg, -⟩ := isRegularLocalRing_quotient hx hx2
  have hprime : (span {x} : Ideal S).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hxp : Prime x := (Ideal.span_singleton_prime hx0).mp hprime
  rw [UniqueFactorizationMonoid.iff_localizationAway_of_prime hxp]
  let A := Localization.Away x
  have : IsDomain A := Localization.Away.isDomain hx0
  apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
  intro P hP hP1
  have hP0 : P ≠ ⊥ := P.ne_bot_of_height_eq_one hP1
  have : Module.FinitePresentation A P := Module.finitePresentation_of_finite A P

  have hPproj : Module.Projective A P := by
    apply Module.projective_of_localization_maximal
    intro q hq
    obtain ⟨hregq, hltq⟩ := isRegularLocalRing_localization_away_atPrime hx q
    let Aq := Localization.AtPrime q
    have : UniqueFactorizationMonoid Aq := ih _ (hn ▸ hltq) Aq rfl
    have hPq : (P.map (algebraMap A Aq)).IsPrincipal := by
      by_cases hle : P ≤ q
      · have hdisj : Disjoint (q.primeCompl : Set A) (P : Set A) := by
          rw [Set.disjoint_left]
          intro a ha haP
          exact ha (hle haP)
        have : (P.map (algebraMap A Aq)).IsPrime :=
          IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl Aq P hP hdisj
        exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
          (by rw [IsLocalization.height_map_of_disjoint q.primeCompl P hdisj, hP1])
      · obtain ⟨a, haP, haq⟩ := Set.not_subset.mp hle
        have htop : P.map (algebraMap A Aq) = ⊤ := Ideal.eq_top_of_isUnit_mem _
          (Ideal.mem_map_of_mem _ haP) (IsLocalization.map_units Aq (⟨a, haq⟩ : q.primeCompl))
        rw [htop]
        exact ⟨⟨1, Ideal.span_singleton_one.symm⟩⟩
    let f := Algebra.linearMap A Aq
    let g := P.toLocalized' Aq q.primeCompl f
    let e := ((IsLocalizedModule.linearEquiv q.primeCompl (LocalizedModule.mkLinearMap q.primeCompl P)
      g).extendScalarsOfIsLocalization q.primeCompl Aq).trans
      (LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map Aq q.primeCompl P))
    obtain ⟨⟨c, hc⟩⟩ := hPq
    have hfree : Module.Free Aq (P.map (algebraMap A Aq)) := by
      by_cases hc0 : c = 0
      · have : Subsingleton (P.map (algebraMap A Aq)) := by
          rw [hc, hc0, Submodule.span_singleton_eq_bot.mpr rfl]
          infer_instance
        infer_instance
      · exact Module.Free.of_equiv ((LinearEquiv.toSpanNonzeroSingleton Aq Aq c hc0).trans
          (LinearEquiv.ofEq _ _ hc.symm))
    exact Module.Projective.of_equiv e.symm

  let Q := P.comap (algebraMap S A)
  have hQpd := hasProjectiveDimensionLT_of_isRegularLocalRing hd Q
  let T := Submonoid.powers x
  let f := Algebra.linearMap S A
  let gQ := Q.toLocalized' A T f
  have hloc : Q.localized' A T f = P := by
    rw [Ideal.localized'_eq_map]; exact IsLocalization.map_comap T A P
  let eQ : LocalizedModule T Q ≃ₗ[A] P :=
    ((IsLocalizedModule.linearEquiv T (LocalizedModule.mkLinearMap T Q) gQ
      ).extendScalarsOfIsLocalization T A).trans (LinearEquiv.ofEq _ _ hloc)
  have hproj' : Module.Projective A (LocalizedModule T Q) := Module.Projective.of_equiv eQ.symm
  have hsf := isStablyFree_localizedModule T n Q hQpd hproj'
  have : IsStablyFree A P := IsStablyFree.equiv eQ
  exact isPrincipal_of_isStablyFree P hP0

instance (priority := 100) IsRegularLocalRing.toUniqueFactorizationMonoid {R : Type u} [CommRing R]
    [IsRegularLocalRing R] : UniqueFactorizationMonoid R :=
  IsRegularLocalRing.uniqueFactorizationMonoid R

/- English proof (translation)
The claim follows from `inferInstance`.
-/
theorem IsRegularLocalRing.isIntegrallyClosed (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsIntegrallyClosed R :=
  inferInstance

end GroundTheory.Arith.SchemeCoh

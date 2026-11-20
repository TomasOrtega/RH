import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocChar
open IsLocalRing UpperTheory.V.Hi

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro y`. Simplify using the standard rewrite rules. Consider the case `succ n ih => intro y`. Rewrite using `[pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]`.
-/
private theorem restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {Y : Submodule A M}
    {t : Module.End A Y} {φ : Module.End A M} (h : Restr t φ) (n : ℕ) : Restr (t ^ n) (φ ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih => intro y; rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

/- English proof (translation)
Establish `hmono : ∀ (i : ι) (k : ℕ), Monotone fun n : ℕ => (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A _ (a i)) ^ n)`. Introduce `i k`. Use `monotone_nat_of_le_succ fun n x hx => ?_` and prove the remaining obligations. Rewrite `hx`, the goal using `[Submodule.mem_comap]`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `r hr z hz`. Rewrite using `[map_smul]`. Use `Submodule.smul_mem_smul hr ?_` and prove the remaining obligations. Rewrite using `[← hu i ⟨z, hz⟩]`.

Conclude with `(u i ⟨z, hz⟩).2`. Introduce `b c hb hc`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ hb hc`. Unfold `locPart`.

Rewrite using `[Submodule.mem_inf, and_iff_right y.2]`. Simplify using `only [Submodule.mem_iInf]`. Use `forall_congr' fun i => forall_congr' fun k => ?_` and prove the remaining obligations. Rewrite using `[Submodule.mem_iSup_of_directed _ (hmono i k).directed_le]`. Use `exists_congr fun n => ?_` and prove the remaining obligations.

Rewrite using `[Submodule.mem_comap, Submodule.mem_smul_top_iff, restr_pow (hu i) n y]`.
-/
private theorem mem_locPart_iff {A M ι : Type} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {op : ι → Module.End A M} {a : ι → A} (u : ι → Module.End A Y)
    (hu : ∀ i, Restr (u i) (op i - algebraMap A _ (a i))) (y : Y) :
    (y : M) ∈ locPart Y op a ↔
      ∀ (i : ι) (k : ℕ), ∃ n : ℕ, (u i ^ n) y ∈ maximalIdeal A ^ k • (⊤ : Submodule A Y) := by
  have hmono : ∀ (i : ι) (k : ℕ), Monotone fun n : ℕ =>
      (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A _ (a i)) ^ n) := by
    intro i k
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr z hz
      rw [map_smul]
      refine Submodule.smul_mem_smul hr ?_
      rw [← hu i ⟨z, hz⟩]
      exact (u i ⟨z, hz⟩).2
    · intro b c hb hc
      rw [map_add]
      exact Submodule.add_mem _ hb hc
  unfold locPart
  rw [Submodule.mem_inf, and_iff_right y.2]
  simp only [Submodule.mem_iInf]
  refine forall_congr' fun i => forall_congr' fun k => ?_
  rw [Submodule.mem_iSup_of_directed _ (hmono i k).directed_le]
  refine exists_congr fun n => ?_
  rw [Submodule.mem_comap, Submodule.mem_smul_top_iff, restr_pow (hu i) n y]

/- English proof (translation)
Introduce `A M ι _ _ _ _ Y _ op a hC T T' _ _ _ _ j j' hj hjr hj' hjr'`. Establish `ht0 : ∀ i, ∃ s : T, Restr (j s) (op i)`. Introduce `i`. Establish `h : (op i).restrict (hC.1 i) ∈ j.range`. Rewrite using `[hjr]`.

Conclude with `Algebra.subset_adjoin ⟨i, fun _ => rfl⟩`. Take `⟨s, hs⟩` from `h`. Use `⟨s, fun y => ?_⟩` and prove the remaining obligations. Establish `hs' : j s = (op i).restrict (hC.1 i)` using `hs`. Rewrite using `[hs']`.

Both sides reduce to the same expression. Use `choose t ht using ht0`. Establish `hset : ∀ (Z : Submodule A M) (ρ : T →ₐ[A] Module.End A Z), (∀ i, Restr (ρ (t i)) (op i)) → (Algebra.adjoin A (Set.range t)).map ρ = heckeAlg Z op`. Introduce `Z ρ hρ`. Rewrite using `[AlgHom.map_adjoin, heckeAlg]`.

Use `congr 1`. Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `⟨i, hρ i⟩`.

Introduce and unpack `⟨i, hi⟩`. Conclude with `⟨t i, ⟨i, rfl⟩, LinearMap.ext fun y => Subtype.ext ((hρ i y).trans (hi y).symm)⟩`. Establish `hgen : Algebra.adjoin A (Set.range t) = ⊤`. Use `eq_top_iff.2 fun s _ => ?_` and prove the remaining obligations. Establish `h : j s ∈ (Algebra.adjoin A (Set.range t)).map j`.

Rewrite using `[hset Y j ht, ← hjr]`. Conclude with `⟨s, rfl⟩`. Take `⟨s', hs', h'⟩` from `h`. Rewrite using `[← hj h']` and apply the resulting hypothesis. Use `haveI : IsNoetherian A (Module.End A Y) := isNoetherian_linearMap A Y Y`.

Use `haveI : Module.Finite A T := Module.Finite.of_injective j.toLinearMap hj`. Take `⟨e, he, hnil, h1e, -, -⟩` from `UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a hgen`. Establish `hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A T), ∀ y, j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y)`. Introduce `μ hμ`. Use `Submodule.span_induction (p := fun μ _ => ∀ y, j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y)) ?_ ?_ ?_ ?_ hμ` and prove the remaining obligations.

Introduce and unpack `_ ⟨c, hc, rfl⟩ y`. Rewrite using `[AlgHom.commutes, Module.algebraMap_end_apply]`. Conclude with `Submodule.smul_mem_smul hc Submodule.mem_top`. Introduce `y`. Simplify using the standard rewrite rules.

Introduce `b c _ _ hb hc y`. Rewrite using `[map_add, LinearMap.add_apply]`. Conclude with `Submodule.add_mem _ (hb y) (hc y)`. Introduce `b c _ hc y`. Rewrite using `[smul_eq_mul, mul_comm, map_mul, Module.End.mul_apply]`.

Conclude with `hc _`. Establish `hL : ∀ y : Y, (y : M) ∈ locPart Y op a ↔ j e y = y`. Introduce `y`. Rewrite using `[mem_locPart_iff (fun i => j (t i - algebraMap A T (a i)))]`. Conclude with `(UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar A Y T ι (j : T →+* Module.End A Y) _ _ e hI he hnil h1e y).symm`.

Introduce `i z`. Rewrite using `[map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, ht i z]`. Both sides reduce to the same expression. Establish `hpres : ∀ (s : T) (y : locPart Y op a), (j s ⟨y, y.2.1⟩ : M) ∈ locPart Y op a`. Introduce `s y`.

Rewrite using `[hL, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply, (hL ⟨y, y.2.1⟩).1 y.2]`. Establish `he' : ∀ y : Y, (j e y : M) ∈ locPart Y op a`. Introduce `y`. Rewrite using `[hL, ← Module.End.mul_apply, ← map_mul, he.eq]`. Set `ρ0 : T → Module.End A (locPart Y op a)` to `fun s => LinearMap.codRestrict _ (Y.subtype ∘ₗ j s ∘ₗ Submodule.inclusion inf_le_left) (hpres s)`.

Establish `hρ0 : ∀ s y, (ρ0 s y : M) = j s ⟨y, y.2.1⟩` using `fun _ _ => rfl`. Set `ρ : T →ₐ[A] Module.End A (locPart Y op a)` to `{ toFun := ρ0 map_one' := by ext y; rw [hρ0, map_one]; rfl map_mul' := fun s s' => by ext y; rw [hρ0, map_mul]; rfl map_zero' := by ext y; rw [hρ0, map_zero]; rfl map_add' := fun s s' => by ext y; rw [hρ0, map_add]; rfl commutes' := fun c => by ext y; rw [hρ0, AlgHom.commutes]; r …`. Establish `hρ : ∀ s y, (ρ s y : M) = j s ⟨y, y.2.1⟩` using `fun _ _ => rfl`. Establish `hrange : ρ.range = j'.range`. Rewrite using `[hjr', ← hset _ ρ (fun i y => by rw [hρ, ht i]), hgen, Algebra.map_top]`.

Set `r : T →ₐ[A] T'` to `(AlgEquiv.ofInjective j' hj').symm.toAlgHom.comp (ρ.codRestrict j'.range fun s => hrange ▸ ⟨s, rfl⟩)`. Establish `hr : ∀ s, j' (r s) = ρ s` using `fun s => congrArg Subtype.val ((AlgEquiv.ofInjective j' hj').apply_symm_apply (ρ.codRestrict j'.range (fun s => hrange ▸ ⟨s, rfl⟩) s))`. Establish `hsurj : Function.Surjective r`. Introduce `s'`. Establish `h : j' s' ∈ ρ.range` using `hrange ▸ ⟨s', rfl⟩`.

Take `⟨s, hs⟩` from `h`. Conclude with `⟨s, hj' ((hr s).trans hs)⟩`. Use `⟨r, hsurj, fun s y => by rw [hr, hρ], fun R _ _ x hx hxt => ?_⟩` and prove the remaining obligations. Establish `hle : (maximalIdeal A).map (algebraMap A T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap A T (a i)) ≤ (maximalIdeal R).comap x`. Use `sup_le (Ideal.map_le_iff_le_comap.2 fun c hc => hx c hc) (Ideal.span_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `hxt i (t i) (ht i)` as an intermediate fact. Rewrite `this` using `[← map_sub]`. Then use the resulting hypothesis. Establish `hxe : x e = 1`. Establish `h1 : 1 - x e ∈ maximalIdeal R`.

Use `hle h1e` as an intermediate fact. Rewrite `this` using `[Ideal.mem_comap, map_sub, map_one]`. Then use the resulting hypothesis. Establish `h2 : IsUnit (x e)`. Use `isUnit_one_sub_self_of_mem_nonunits _ h1` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.

Conclude with `h2.mul_left_cancel (by rw [← map_mul, he.eq, mul_one])`. Use `⟨fun hb => ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : e = 0`. Use `hj ?_` and prove the remaining obligations. Rewrite using `[map_zero]`.

Use extensionality with `y`. Use `he' y` as an intermediate fact. Rewrite `this` using `[hb]`. Conclude with `this`. Rewrite `hxe` using `[h0, map_zero]`.

Conclude with `zero_ne_one hxe`. Establish `hker : RingHom.ker (r : T →+* T') ≤ RingHom.ker x`. Introduce `s hs`. Establish `hs0 : r s = 0` using `hs`. Establish `h0 : s * e = 0`.

Use `hj ?_` and prove the remaining obligations. Use extensionality with `y`. Use `hρ s ⟨_, he' y⟩` as an intermediate fact. Rewrite `this` using `[← hr, hs0, map_zero]`. Rewrite using `[map_mul, map_zero]`.

Conclude with `this.symm`. Rewrite using `[RingHom.mem_ker, ← mul_one (x s), ← hxe, ← map_mul, h0, map_zero]`. Conclude with `⟨(r : T →+* T').liftOfSurjective hsurj ⟨x, hker⟩, RingHom.liftOfRightInverse_comp _ _ _ _⟩`.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeRestr :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → ∀ (T T' : Type) [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (j : T →ₐ[A] Module.End A Y) (j' : T' →ₐ[A] Module.End A (locPart Y op a)), Function.Injective j → j.range = heckeAlg Y op → Function.Injective j' → j'.range = heckeAlg (locPart Y op a) op → ∃ r : T →ₐ[A] T', Function.Surjective r ∧ (∀ (s : T) (y : locPart Y op a), (j' (r s) y : M) = j s ⟨y, y.2.1⟩) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : T →+* R), (∀ c ∈ maximalIdeal A, x (algebraMap A T c) ∈ maximalIdeal R) → (∀ i s, Restr (j s) (op i) → x s - x (algebraMap A T (a i)) ∈ maximalIdeal R) → locPart Y op a ≠ ⊥ ∧ ∃ x' : T' →+* R, x'.comp (r : T →+* T') = x := by
  intro A M ι _ _ _ _ Y _ op a hC T T' _ _ _ _ j j' hj hjr hj' hjr'
  have ht0 : ∀ i, ∃ s : T, Restr (j s) (op i) := by
    intro i
    have h : (op i).restrict (hC.1 i) ∈ j.range := by
      rw [hjr]
      exact Algebra.subset_adjoin ⟨i, fun _ => rfl⟩
    obtain ⟨s, hs⟩ := h
    refine ⟨s, fun y => ?_⟩
    have hs' : j s = (op i).restrict (hC.1 i) := hs
    rw [hs']
    rfl
  choose t ht using ht0
  have hset : ∀ (Z : Submodule A M) (ρ : T →ₐ[A] Module.End A Z), (∀ i, Restr (ρ (t i)) (op i)) →
      (Algebra.adjoin A (Set.range t)).map ρ = heckeAlg Z op := by
    intro Z ρ hρ
    rw [AlgHom.map_adjoin, heckeAlg]
    congr 1
    ext φ
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, hρ i⟩
    · rintro ⟨i, hi⟩
      exact ⟨t i, ⟨i, rfl⟩, LinearMap.ext fun y => Subtype.ext ((hρ i y).trans (hi y).symm)⟩
  have hgen : Algebra.adjoin A (Set.range t) = ⊤ := by
    refine eq_top_iff.2 fun s _ => ?_
    have h : j s ∈ (Algebra.adjoin A (Set.range t)).map j := by
      rw [hset Y j ht, ← hjr]
      exact ⟨s, rfl⟩
    obtain ⟨s', hs', h'⟩ := h
    rwa [← hj h']
  haveI : IsNoetherian A (Module.End A Y) := isNoetherian_linearMap A Y Y
  haveI : Module.Finite A T := Module.Finite.of_injective j.toLinearMap hj
  obtain ⟨e, he, hnil, h1e, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a hgen
  have hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A T), ∀ y,
      j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y) := by
    intro μ hμ
    refine Submodule.span_induction (p := fun μ _ => ∀ y,
      j μ y ∈ maximalIdeal A • (⊤ : Submodule A Y)) ?_ ?_ ?_ ?_ hμ
    · rintro _ ⟨c, hc, rfl⟩ y
      rw [AlgHom.commutes, Module.algebraMap_end_apply]
      exact Submodule.smul_mem_smul hc Submodule.mem_top
    · intro y; simp
    · intro b c _ _ hb hc y
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ (hb y) (hc y)
    · intro b c _ hc y
      rw [smul_eq_mul, mul_comm, map_mul, Module.End.mul_apply]
      exact hc _
  have hL : ∀ y : Y, (y : M) ∈ locPart Y op a ↔ j e y = y := by
    intro y
    rw [mem_locPart_iff (fun i => j (t i - algebraMap A T (a i)))]
    · exact (UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar A Y T ι (j : T →+* Module.End A Y) _ _ e hI he hnil h1e y).symm
    · intro i z
      rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub, ht i z]
      rfl
  have hpres : ∀ (s : T) (y : locPart Y op a), (j s ⟨y, y.2.1⟩ : M) ∈ locPart Y op a := by
    intro s y
    rw [hL, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply,
      (hL ⟨y, y.2.1⟩).1 y.2]
  have he' : ∀ y : Y, (j e y : M) ∈ locPart Y op a := by
    intro y
    rw [hL, ← Module.End.mul_apply, ← map_mul, he.eq]
  let ρ0 : T → Module.End A (locPart Y op a) := fun s =>
    LinearMap.codRestrict _ (Y.subtype ∘ₗ j s ∘ₗ Submodule.inclusion inf_le_left) (hpres s)
  have hρ0 : ∀ s y, (ρ0 s y : M) = j s ⟨y, y.2.1⟩ := fun _ _ => rfl
  let ρ : T →ₐ[A] Module.End A (locPart Y op a) :=
    { toFun := ρ0
      map_one' := by ext y; rw [hρ0, map_one]; rfl
      map_mul' := fun s s' => by ext y; rw [hρ0, map_mul]; rfl
      map_zero' := by ext y; rw [hρ0, map_zero]; rfl
      map_add' := fun s s' => by ext y; rw [hρ0, map_add]; rfl
      commutes' := fun c => by ext y; rw [hρ0, AlgHom.commutes]; rfl }
  have hρ : ∀ s y, (ρ s y : M) = j s ⟨y, y.2.1⟩ := fun _ _ => rfl
  have hrange : ρ.range = j'.range := by
    rw [hjr', ← hset _ ρ (fun i y => by rw [hρ, ht i]), hgen, Algebra.map_top]
  let r : T →ₐ[A] T' := (AlgEquiv.ofInjective j' hj').symm.toAlgHom.comp
    (ρ.codRestrict j'.range fun s => hrange ▸ ⟨s, rfl⟩)
  have hr : ∀ s, j' (r s) = ρ s := fun s =>
    congrArg Subtype.val ((AlgEquiv.ofInjective j' hj').apply_symm_apply
      (ρ.codRestrict j'.range (fun s => hrange ▸ ⟨s, rfl⟩) s))
  have hsurj : Function.Surjective r := by
    intro s'
    have h : j' s' ∈ ρ.range := hrange ▸ ⟨s', rfl⟩
    obtain ⟨s, hs⟩ := h
    exact ⟨s, hj' ((hr s).trans hs)⟩
  refine ⟨r, hsurj, fun s y => by rw [hr, hρ], fun R _ _ x hx hxt => ?_⟩
  have hle : (maximalIdeal A).map (algebraMap A T) ⊔
      Ideal.span (Set.range fun i => t i - algebraMap A T (a i)) ≤ (maximalIdeal R).comap x := by
    refine sup_le (Ideal.map_le_iff_le_comap.2 fun c hc => hx c hc) (Ideal.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    have := hxt i (t i) (ht i)
    rwa [← map_sub] at this
  have hxe : x e = 1 := by
    have h1 : 1 - x e ∈ maximalIdeal R := by
      have := hle h1e
      rwa [Ideal.mem_comap, map_sub, map_one] at this
    have h2 : IsUnit (x e) := by
      have := isUnit_one_sub_self_of_mem_nonunits _ h1
      rwa [sub_sub_cancel] at this
    exact h2.mul_left_cancel (by rw [← map_mul, he.eq, mul_one])
  refine ⟨fun hb => ?_, ?_⟩
  · have h0 : e = 0 := by
      refine hj ?_
      rw [map_zero]
      ext y
      have := he' y
      rw [hb] at this
      exact this
    rw [h0, map_zero] at hxe
    exact zero_ne_one hxe
  · have hker : RingHom.ker (r : T →+* T') ≤ RingHom.ker x := by
      intro s hs
      have hs0 : r s = 0 := hs
      have h0 : s * e = 0 := by
        refine hj ?_
        ext y
        have := hρ s ⟨_, he' y⟩
        rw [← hr, hs0, map_zero] at this
        rw [map_mul, map_zero]
        exact this.symm
      rw [RingHom.mem_ker, ← mul_one (x s), ← hxe, ← map_mul, h0, map_zero]
    exact ⟨(r : T →+* T').liftOfSurjective hsurj ⟨x, hker⟩,
      RingHom.liftOfRightInverse_comp _ _ _ _⟩

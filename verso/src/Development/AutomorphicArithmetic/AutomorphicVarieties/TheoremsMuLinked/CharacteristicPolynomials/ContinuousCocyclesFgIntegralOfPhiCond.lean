import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.LocallyConstantCocyclesFiniteOfPhi
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ContinuousResP
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

/- English proof (translation)
Rewrite using `[Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, hy⟩`. Conclude with `⟨y, hy⟩`. Introduce and unpack `⟨y, hy⟩`.

Conclude with `⟨y, Submodule.mem_top, hy⟩`.
-/
private theorem mem_pow_smul {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (t : A) (N : ℕ) (x : M) :
    x ∈ (Ideal.span {t} ^ N • (⊤ : Submodule A M)) ↔ ∃ y, t ^ N • y = x := by
  rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, -, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Submodule.mem_top, hy⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations. Introduce `r hr n _ i`. Simplify using `using J.mul_mem_right (n i) hr`.

Introduce `a b ha hb i`. Simplify using `using J.add_mem (ha i) (hb i)`. Introduce `hx`. Establish `hsum : x = ∑ i, x i • (Pi.single i (1 : R) : Fin r → R)`. Use extensionality with `j`.

Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hsum]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top`.
-/
private theorem mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr n _ i
      simpa using J.mul_mem_right (n i) hr
    · intro a b ha hb i
      simpa using J.add_mem (ha i) (hb i)
  · intro hx
    have hsum : x = ∑ i, x i • (Pi.single i (1 : R) : Fin r → R) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

/- English proof (translation)
Establish `key : ∀ a b : Fin r → R, (J • (⊤ : Submodule R (Fin r → R))).mkQ a = (J • (⊤ : Submodule R (Fin r → R))).mkQ b ↔ ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i)`. Introduce `a b`. Simplify using `only [Submodule.mkQ_apply, Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_pi]`. Both sides reduce to the same expression. Simplify using `only [IsLocallyConstant.iff_eventually_eq, key]`.

Prove the components needed by the constructor for the conclusion. Introduce `h i x`. Conclude with `(h x).mono fun y hy => hy i`. Introduce `h x`. Conclude with `Filter.eventually_all.mpr fun i => h i x`.
-/
private theorem lc_iff {R G : Type} [CommRing R] [TopologicalSpace G] (J : Ideal R) {r : ℕ} (f : G → Fin r → R) :
    (IsLocallyConstant fun g => (J • (⊤ : Submodule R (Fin r → R))).mkQ (f g)) ↔
      ∀ i, IsLocallyConstant fun g => Ideal.Quotient.mk J (f g i) := by
  have key : ∀ a b : Fin r → R, (J • (⊤ : Submodule R (Fin r → R))).mkQ a = (J • (⊤ : Submodule R (Fin r → R))).mkQ b ↔
      ∀ i, Ideal.Quotient.mk J (a i) = Ideal.Quotient.mk J (b i) := by
    intro a b
    simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, Ideal.Quotient.eq, mem_smul_top_pi]
    rfl
  simp only [IsLocallyConstant.iff_eventually_eq, key]
  constructor
  · intro h i x
    exact (h x).mono fun y hy => hy i
  · intro h x
    exact Filter.eventually_all.mpr fun i => h i x

/- English proof (translation)
Substitute `hI` using the available equality. Establish `htinj : ∀ x : M, t • x = 0 → x = 0`. Introduce `x hx`. Set `b` to `Module.Free.chooseBasis R M`. Apply `b.repr.injective` to reduce the goal to its premises.

Use extensionality with `i`. Establish `h` using `congrArg (fun y => b.repr y i) hx`. Simplify using `only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h`. Simplify using `using (mul_eq_zero.mp h).resolve_left ht0`. Establish `hcancel : ∀ a b : M, t • a = t • b → a = b` using `fun a b h => sub_eq_zero.mp (htinj _ (by rw [smul_sub, h, sub_self]))`.

Establish `hMh : ∀ x : M, (∀ n : ℕ, ∃ y, t ^ n • y = x) → x = 0`. Introduce `x hx`. Establish `hle : Ideal.span {t} ≤ (⊥ : Ideal R).jacobson`. Rewrite using `[IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]`. Conclude with `IsLocalRing.le_maximalIdeal hIne`.

Establish `h` using `Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) _ hle`. Establish `hx' : x ∈ ⨅ i, Ideal.span {t} ^ i • (⊤ : Submodule R M)` using `(Submodule.mem_iInf _).mpr fun n => (mem_pow_smul t n x).mpr (hx n)`. Rewrite `hx'` using `[h]`. Simplify using `using hx'`. Set `C : Submodule R (G → M)` to `{ carrier := {z | (∀ N : ℕ, IsLocallyConstant fun g => (Ideal.span {t} ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧ ∀ g h, z (g * h) = z g + ρ g (z h)} add_mem' := by`.

Introduce and unpack `a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩`. Use `⟨fun N => ?_, fun g h => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.add_apply, map_add]`. Conclude with `(ha1 N).add (hb1 N)`. Simplify using `only [Pi.add_apply, ha2, hb2, map_add]`.

Normalize the expressions using the abelian group laws. Use the proof step `zero_mem' := ⟨fun N => by`. Simplify using `only [Pi.zero_apply, map_zero]`. Conclude with `IsLocallyConstant.const 0,`. Use `fun g h => by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `r a ⟨ha1, ha2⟩`. Use `⟨fun N => ?_, fun g h => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, map_smul]`. Conclude with `(ha1 N).comp (fun q => r • q)`.

Simplify using `only [Pi.smul_apply, ha2, smul_add, map_smul] }`. Establish `hZC : Z ≤ C` using `fun z hz => hZ z hz`. Use `haveI : Finite (R ⧸ Ideal.span {t}) := hfq`. Use `haveI hM'fin : Finite (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) := Module.finite_of_finite (R ⧸ Ideal.span {t})`. Set `ρ' : G →* AddMonoid.End (M ⧸ Ideal.span {t} • (⊤ : Submodule R M))` to `{ toFun := fun g => ((Ideal.span {t} • (⊤ : Submodule R M)).mapQ _ (ρ g) (Submodule.smul_top_le_comap_smul_top _ _)).toAddMonoidHom map_one' := by`.

Use `AddMonoidHom.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H x`. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Use the proof step `map_mul' := by`. Introduce `g h`. Use `AddMonoidHom.ext fun x => ?_` and prove the remaining obligations. Proceed by induction on `x using Submodule.Quotient.induction_on with`. Consider the case `H x`.

Simplify using `[Module.End.mul_apply]`. Use `rfl }`. Establish `hρ' : ∀ g x, ρ' g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x)` using `fun g x => rfl`. Establish `hS` using `UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi l ρ' hΦ (by`. Introduce `m`.

Proceed by induction on `m using Submodule.Quotient.induction_on with`. Consider the case `H x`. Rewrite using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul R]`. Conclude with `Submodule.smul_mem_smul hlI Submodule.mem_top)`. Use the proof step `(by`.

Introduce `m`. Proceed by induction on `m using Submodule.Quotient.induction_on with`. Consider the case `H x`. Establish `h1` using `hρ 1 x`. Rewrite `h1` using `[pow_one]`.

Conclude with `h1)`. Set `Ψ : C →ₗ[R] (G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M))` to `LinearMap.pi fun g => (Ideal.span {t} • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.proj g ∘ₗ C.subtype)`. Establish `hΨ : ∀ z g, Ψ z g = Submodule.Quotient.mk (z.1 g)` using `fun z g => rfl`. Establish `hrange : ∀ z, Ψ z ∈ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ' g (z h)}`. Introduce `z`.

Take `⟨hz1, hz2⟩` from `z.2`. Use `⟨?_, fun g h => ?_⟩` and prove the remaining obligations. Establish `h1` using `hz1 1`. Rewrite `h1` using `[pow_one]`. Conclude with `h1`.

Rewrite using `[hΨ, hΨ, hΨ, hz2, hρ', Submodule.Quotient.mk_add]`. Establish `hker : LinearMap.ker Ψ = Ideal.span {t} • (⊤ : Submodule R C)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `z hz`. Establish `hz' : ∀ g, ∃ y, t • y = z.1 g`.

Introduce `g`. Establish `h0 : Ψ z g = 0` using `congrFun (LinearMap.mem_ker.mp hz) g`. Rewrite `h0` using `[hΨ, Submodule.Quotient.mk_eq_zero, ← pow_one (Ideal.span {t})]`. Take `⟨y, hy⟩` from `(mem_pow_smul t 1 _).mp h0`. Conclude with `⟨y, by simpa using hy⟩`.

Use `choose y hy using hz'`. Take `⟨hz1, hz2⟩` from `z.2`. Establish `hyC : y ∈ C`. Use `⟨fun N => ?_, fun g h => ?_⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`.

Introduce `x`. Use `filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (hz1 (N + 1)) x] with g hg`. Rewrite `hg`, the goal using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]`. Take `⟨w, hw⟩` from `(mem_pow_smul t (N + 1) _).mp hg`. Use `(mem_pow_smul t N _).mpr ⟨w, hcancel _ _ ?_⟩` and prove the remaining obligations.

Rewrite using `[smul_sub, hy, hy, ← hw, ← mul_smul, ← pow_succ']`. Apply `hcancel` to reduce the goal to its premises. Rewrite using `[hy (g * h), smul_add, ← map_smul, hy g, hy h]`. Conclude with `hz2 g h`. Establish `hzt : z = t • (⟨y, hyC⟩ : C)` using `Subtype.ext (funext fun g => (hy g).symm)`.

Rewrite using `[hzt]`. Conclude with `Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top`. Introduce `z hz`. Use `Submodule.smul_induction_on hz ?_ ?_` and prove the remaining obligations. Introduce `r hr n _`.

Rewrite using `[LinearMap.mem_ker, map_smul]`. Use function extensionality and compare the values at `g`. Rewrite using `[Pi.smul_apply, hΨ, ← Submodule.Quotient.mk_smul, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `Submodule.smul_mem_smul hr Submodule.mem_top`. Introduce `a b ha hb`.

Conclude with `add_mem ha hb`. Establish `hfin : Finite (C ⧸ LinearMap.ker Ψ)`. Establish `hsub : (LinearMap.range Ψ : Set _) ⊆ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧ ∀ g h, z (g * h) = z g + ρ' g (z h)}`. Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `hrange z`.

Use `haveI : Finite (LinearMap.range Ψ) := (hS.subset hsub).to_subtype`. Conclude with `Finite.of_equiv _ Ψ.quotKerEquivRange.symm.toEquiv`. Rewrite `hfin` using `[hker]`. Use `haveI : IsHausdorff (Ideal.span {t}) C := by`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `g`. Use `show x.1 g = 0`. Apply `hMh` to reduce the goal to its premises. Introduce `n`.

Establish `h1` using `hx n`. Rewrite `h1` using `[SModEq.sub_mem, sub_zero]`. Take `⟨y, hy⟩` from `(mem_pow_smul t n x).mp h1`. Conclude with `⟨y.1 g, by rw [← hy]; rfl⟩`. Use `haveI : Module.Finite R (C ⧸ Ideal.span {t} • (⊤ : Submodule R C)) := Module.Finite.of_finite`.

Establish `hCfin : Module.Finite R C` using `(UpperTheory.V.abelian₂.nakayama R (Ideal.span {t}) C).2 this`. Establish `hCfg : C.FG` using `Module.Finite.iff_fg.mp hCfin`. Use `haveI := isNoetherian_of_fg_of_noetherian C hCfg`. Establish `hZ'fg : (Z.comap C.subtype).FG` using `IsNoetherian.noetherian _`. Establish `hZeq : Submodule.map C.subtype (Z.comap C.subtype) = Z` using `Submodule.map_comap_eq_of_le (by rwa [Submodule.range_subtype])`.

Rewrite using `[← hZeq]`. Conclude with `hZ'fg.map _`.
-/
private theorem cocycles_finitely_generated (l : ℕ) [Fact l.Prime] {R G M : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (t : R) (I : Ideal R) (hI : I = Ideal.span {t}) (ht0 : t ≠ 0) (hIne : I ≠ ⊤) [IsPrecomplete I R]
    (hfq : Finite (R ⧸ I)) (hlI : (l : R) ∈ I)
    (ρ : G →* Module.End R M) (Z : Submodule R (G → M)) (hΦ : PhiCond G l)
    (hρ : ∀ (N : ℕ) m, IsLocallyConstant fun g => (I ^ N • (⊤ : Submodule R M)).mkQ (ρ g m))
    (hZ : ∀ z ∈ Z, (∀ N : ℕ, IsLocallyConstant fun g => (I ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧
      ∀ g h, z (g * h) = z g + ρ g (z h)) : Z.FG := by
  subst hI
  have htinj : ∀ x : M, t • x = 0 → x = 0 := by
    intro x hx
    let b := Module.Free.chooseBasis R M
    apply b.repr.injective
    ext i
    have h := congrArg (fun y => b.repr y i) hx
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at h
    simpa using (mul_eq_zero.mp h).resolve_left ht0
  have hcancel : ∀ a b : M, t • a = t • b → a = b := fun a b h =>
    sub_eq_zero.mp (htinj _ (by rw [smul_sub, h, sub_self]))
  have hMh : ∀ x : M, (∀ n : ℕ, ∃ y, t ^ n • y = x) → x = 0 := by
    intro x hx
    have hle : Ideal.span {t} ≤ (⊥ : Ideal R).jacobson := by
      rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact IsLocalRing.le_maximalIdeal hIne
    have h := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) _ hle
    have hx' : x ∈ ⨅ i, Ideal.span {t} ^ i • (⊤ : Submodule R M) :=
      (Submodule.mem_iInf _).mpr fun n => (mem_pow_smul t n x).mpr (hx n)
    rw [h] at hx'
    simpa using hx'
  let C : Submodule R (G → M) :=
    { carrier := {z | (∀ N : ℕ, IsLocallyConstant fun g => (Ideal.span {t} ^ N • (⊤ : Submodule R M)).mkQ (z g)) ∧
        ∀ g h, z (g * h) = z g + ρ g (z h)}
      add_mem' := by
        rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · simp only [Pi.add_apply, map_add]
          exact (ha1 N).add (hb1 N)
        · simp only [Pi.add_apply, ha2, hb2, map_add]
          abel
      zero_mem' := ⟨fun N => by
          simp only [Pi.zero_apply, map_zero]
          exact IsLocallyConstant.const 0,
        fun g h => by simp⟩
      smul_mem' := by
        rintro r a ⟨ha1, ha2⟩
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · simp only [Pi.smul_apply, map_smul]
          exact (ha1 N).comp (fun q => r • q)
        · simp only [Pi.smul_apply, ha2, smul_add, map_smul] }
  have hZC : Z ≤ C := fun z hz => hZ z hz
  haveI : Finite (R ⧸ Ideal.span {t}) := hfq
  haveI hM'fin : Finite (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) := Module.finite_of_finite (R ⧸ Ideal.span {t})
  let ρ' : G →* AddMonoid.End (M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) :=
    { toFun := fun g => ((Ideal.span {t} • (⊤ : Submodule R M)).mapQ _ (ρ g)
        (Submodule.smul_top_le_comap_smul_top _ _)).toAddMonoidHom
      map_one' := by
        refine AddMonoidHom.ext fun x => ?_
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp
          rfl
      map_mul' := by
        intro g h
        refine AddMonoidHom.ext fun x => ?_
        induction x using Submodule.Quotient.induction_on with
        | H x =>
          simp [Module.End.mul_apply]
          rfl }
  have hρ' : ∀ g x, ρ' g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (ρ g x) := fun g x => rfl
  have hS := UpperTheory.V.Pa.Det.locallyConstant_cocycles_finite_of_phi l ρ' hΦ
    (by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, ← Nat.cast_smul_eq_nsmul R]
        exact Submodule.smul_mem_smul hlI Submodule.mem_top)
    (by
      intro m
      induction m using Submodule.Quotient.induction_on with
      | H x =>
        have h1 := hρ 1 x
        rw [pow_one] at h1
        exact h1)
  let Ψ : C →ₗ[R] (G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M)) :=
    LinearMap.pi fun g => (Ideal.span {t} • (⊤ : Submodule R M)).mkQ ∘ₗ (LinearMap.proj g ∘ₗ C.subtype)
  have hΨ : ∀ z g, Ψ z g = Submodule.Quotient.mk (z.1 g) := fun z g => rfl
  have hrange : ∀ z, Ψ z ∈ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧
      ∀ g h, z (g * h) = z g + ρ' g (z h)} := by
    intro z
    obtain ⟨hz1, hz2⟩ := z.2
    refine ⟨?_, fun g h => ?_⟩
    · have h1 := hz1 1
      rw [pow_one] at h1
      exact h1
    · rw [hΨ, hΨ, hΨ, hz2, hρ', Submodule.Quotient.mk_add]
  have hker : LinearMap.ker Ψ = Ideal.span {t} • (⊤ : Submodule R C) := by
    apply le_antisymm
    · intro z hz
      have hz' : ∀ g, ∃ y, t • y = z.1 g := by
        intro g
        have h0 : Ψ z g = 0 := congrFun (LinearMap.mem_ker.mp hz) g
        rw [hΨ, Submodule.Quotient.mk_eq_zero, ← pow_one (Ideal.span {t})] at h0
        obtain ⟨y, hy⟩ := (mem_pow_smul t 1 _).mp h0
        exact ⟨y, by simpa using hy⟩
      choose y hy using hz'
      obtain ⟨hz1, hz2⟩ := z.2
      have hyC : y ∈ C := by
        refine ⟨fun N => ?_, fun g h => ?_⟩
        · rw [IsLocallyConstant.iff_eventually_eq]
          intro x
          filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (hz1 (N + 1)) x] with g hg
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hg ⊢
          obtain ⟨w, hw⟩ := (mem_pow_smul t (N + 1) _).mp hg
          refine (mem_pow_smul t N _).mpr ⟨w, hcancel _ _ ?_⟩
          rw [smul_sub, hy, hy, ← hw, ← mul_smul, ← pow_succ']
        · apply hcancel
          rw [hy (g * h), smul_add, ← map_smul, hy g, hy h]
          exact hz2 g h
      have hzt : z = t • (⟨y, hyC⟩ : C) := Subtype.ext (funext fun g => (hy g).symm)
      rw [hzt]
      exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t) Submodule.mem_top
    · intro z hz
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro r hr n _
        rw [LinearMap.mem_ker, map_smul]
        funext g
        rw [Pi.smul_apply, hΨ, ← Submodule.Quotient.mk_smul, Pi.zero_apply, Submodule.Quotient.mk_eq_zero]
        exact Submodule.smul_mem_smul hr Submodule.mem_top
      · intro a b ha hb
        exact add_mem ha hb
  have hfin : Finite (C ⧸ LinearMap.ker Ψ) := by
    have hsub : (LinearMap.range Ψ : Set _) ⊆ {z : G → M ⧸ Ideal.span {t} • (⊤ : Submodule R M) | IsLocallyConstant z ∧
        ∀ g h, z (g * h) = z g + ρ' g (z h)} := by
      rintro _ ⟨z, rfl⟩
      exact hrange z
    haveI : Finite (LinearMap.range Ψ) := (hS.subset hsub).to_subtype
    exact Finite.of_equiv _ Ψ.quotKerEquivRange.symm.toEquiv
  rw [hker] at hfin
  haveI : IsHausdorff (Ideal.span {t}) C := by
    refine ⟨fun x hx => ?_⟩
    apply Subtype.ext
    funext g
    show x.1 g = 0
    apply hMh
    intro n
    have h1 := hx n
    rw [SModEq.sub_mem, sub_zero] at h1
    obtain ⟨y, hy⟩ := (mem_pow_smul t n x).mp h1
    exact ⟨y.1 g, by rw [← hy]; rfl⟩
  haveI : Module.Finite R (C ⧸ Ideal.span {t} • (⊤ : Submodule R C)) := Module.Finite.of_finite
  have hCfin : Module.Finite R C := (UpperTheory.V.abelian₂.nakayama R (Ideal.span {t}) C).2 this
  have hCfg : C.FG := Module.Finite.iff_fg.mp hCfin
  haveI := isNoetherian_of_fg_of_noetherian C hCfg
  have hZ'fg : (Z.comap C.subtype).FG := IsNoetherian.noetherian _
  have hZeq : Submodule.map C.subtype (Z.comap C.subtype) = Z :=
    Submodule.map_comap_eq_of_le (by rwa [Submodule.range_subtype])
  rw [← hZeq]
  exact hZ'fg.map _

/- English proof (translation)
Introduce `l _ c G _ _ _ _ _ m σ Z hΦ hσ hZ`. Take `⟨hc, hf, hl, -⟩` from `UpperTheory.V.abelian₂.dvr_finite l c.O`. Take `⟨t, ht⟩` from `IsDiscreteValuationRing.exists_irreducible c.O`. Use `haveI : IsPrecomplete (maximalIdeal c.O) c.O := hc.toIsPrecomplete`. Set `ρ : G →* Module.End c.O (Fin m → c.O)` to `(Matrix.toLinAlgEquiv' (R := c.O) (n := Fin m)).toAlgHom.toRingHom.toMonoidHom.comp (W.mat σ)`.

Establish `hρ : ∀ g x, ρ g x = W.mat σ g *ᵥ x` using `fun g x => rfl`. Use `cocycles_finitely_generated l t (maximalIdeal c.O) ht.maximalIdeal_eq ht.ne_zero (maximalIdeal.isMaximal c.O).ne_top hf hl ρ Z hΦ (fun N x => ?_) (fun z hz => ⟨fun N => ?_, fun g h => ?_⟩)` and prove the remaining obligations. Rewrite using `[lc_iff]`. Introduce `i`. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`.

Introduce `g`. Use `filter_upwards [Filter.eventually_all.2 fun j => (hσ i j N).eventually_eq g] with g' hg'`. Simplify using `only [hρ, Matrix.mulVec, dotProduct, map_sum, map_mul, hg']`. Rewrite using `[lc_iff]`. Conclude with `fun i => (hZ z hz).1 i N`.

Rewrite using `[hρ]`. Conclude with `(hZ z hz).2 g h`.
-/
theorem UpperTheory.V.Th.Det.continuousCocycles_fg_integral_of_phiCond :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {m : ℕ} (σ : G →* GL (Fin m) c.O) (Z : Submodule c.O (G → Fin m → c.O)), PhiCond G l → (∀ i j, AdicCont (maximalIdeal c.O) fun g => W.mat σ g i j) → (∀ z ∈ Z, (∀ i, AdicCont (maximalIdeal c.O) fun g => z g i) ∧ ∀ g h, z (g * h) = z g + W.mat σ g *ᵥ z h) → Z.FG := by
  intro l _ c G _ _ _ _ _ m σ Z hΦ hσ hZ
  obtain ⟨hc, hf, hl, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  haveI : IsPrecomplete (maximalIdeal c.O) c.O := hc.toIsPrecomplete
  let ρ : G →* Module.End c.O (Fin m → c.O) :=
    (Matrix.toLinAlgEquiv' (R := c.O) (n := Fin m)).toAlgHom.toRingHom.toMonoidHom.comp (W.mat σ)
  have hρ : ∀ g x, ρ g x = W.mat σ g *ᵥ x := fun g x => rfl
  refine cocycles_finitely_generated l t (maximalIdeal c.O) ht.maximalIdeal_eq ht.ne_zero (maximalIdeal.isMaximal c.O).ne_top
    hf hl ρ Z hΦ (fun N x => ?_) (fun z hz => ⟨fun N => ?_, fun g h => ?_⟩)
  · rw [lc_iff]
    intro i
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    filter_upwards [Filter.eventually_all.2 fun j => (hσ i j N).eventually_eq g] with g' hg'
    simp only [hρ, Matrix.mulVec, dotProduct, map_sum, map_mul, hg']
  · rw [lc_iff]
    exact fun i => (hZ z hz).1 i N
  · rw [hρ]; exact (hZ z hz).2 g h

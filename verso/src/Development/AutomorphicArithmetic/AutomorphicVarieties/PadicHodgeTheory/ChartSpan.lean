import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
open UpperTheory.V.Loc UpperTheory.V.Alg IsLocalRing

/- English proof (translation)
Rewrite using `[MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map, Finset.Nat.antidiagonal_succ]`. Simplify using the standard rewrite rules.
-/
private theorem coeff1_mul {σ E : Type} [CommRing E] (j : σ) (f g : MvPowerSeries σ E) :
    MvPowerSeries.coeff (Finsupp.single j 1) (f * g) =
      MvPowerSeries.constantCoeff f * MvPowerSeries.coeff (Finsupp.single j 1) g +
        MvPowerSeries.coeff (Finsupp.single j 1) f * MvPowerSeries.constantCoeff g := by
  classical
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map,
    Finset.Nat.antidiagonal_succ]
  simp

/- English proof (translation)
Take `⟨T, hT⟩` from `(IsNoetherian.noetherian (RingHom.ker x) : (RingHom.ker x).FG)`. Take `⟨c, hc⟩` from `IsLocalization.exist_integer_multiples (nonZeroDivisors O) T D`. Use `⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩` and prove the remaining obligations. Establish `h0 : D 0 = 0` using `by simpa using halg 0`. Establish `key : ∀ a ∈ Submodule.span R (T : Set R), ∃ o : O, algebraMap O E o = algebraMap O E c * D a`.

Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem a ha`. Take `⟨o, ho⟩` from `hc a ha`. Conclude with `⟨o, by rw [ho, Algebra.smul_def]⟩`.

Consider the case `zero => exact ⟨0, by simp [h0]⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨o, ho⟩` from `ha`. Take `⟨o', ho'⟩` from `hb`. Conclude with `⟨o + o', by rw [map_add, ho, ho', hadd, mul_add]⟩`.

Consider the case `smul r a ha' ha`. Take `⟨o, ho⟩` from `ha`. Rewrite `ha'` using `[hT]`. Establish `hx : x a = 0` using `ha'`. Conclude with `⟨x r * o, by rw [map_mul, ho, smul_eq_mul, hmul, hx, map_zero]; ring⟩`.

Introduce `a`. Establish `hm : a - algebraMap O R (x a) ∈ RingHom.ker x`. Simplify using `[RingHom.mem_ker]`. Rewrite `hm` using `[← hT]`. Take `⟨o, ho⟩` from `key _ hm`.

Use `⟨o, ?_⟩` and prove the remaining obligations. Establish `: D a = D (a - algebraMap O R (x a))` using `by conv_lhs => rw [← sub_add_cancel a (algebraMap O R (x a))]`. Rewrite using `[hadd, halg, add_zero]`. Rewrite using `[this, ho]`.
-/
private theorem exists_den {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R]
    [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (x : R →ₐ[O] O) (D : R → E)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = algebraMap O E (x a) * D b + D a * algebraMap O E (x b))
    (halg : ∀ o, D (algebraMap O R o) = 0) :
    ∃ c : O, c ≠ 0 ∧ ∀ a, ∃ o : O, algebraMap O E o = algebraMap O E c * D a := by
  classical
  obtain ⟨T, hT⟩ := (IsNoetherian.noetherian (RingHom.ker x) : (RingHom.ker x).FG)
  obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) T D
  refine ⟨c, nonZeroDivisors.ne_zero c.2, ?_⟩
  have h0 : D 0 = 0 := by simpa using halg 0
  have key : ∀ a ∈ Submodule.span R (T : Set R), ∃ o : O, algebraMap O E o = algebraMap O E c * D a := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨o, ho⟩ := hc a ha
      exact ⟨o, by rw [ho, Algebra.smul_def]⟩
    | zero => exact ⟨0, by simp [h0]⟩
    | add a b _ _ ha hb =>
      obtain ⟨o, ho⟩ := ha
      obtain ⟨o', ho'⟩ := hb
      exact ⟨o + o', by rw [map_add, ho, ho', hadd, mul_add]⟩
    | smul r a ha' ha =>
      obtain ⟨o, ho⟩ := ha
      rw [hT] at ha'
      have hx : x a = 0 := ha'
      exact ⟨x r * o, by rw [map_mul, ho, smul_eq_mul, hmul, hx, map_zero]; ring⟩
  intro a
  have hm : a - algebraMap O R (x a) ∈ RingHom.ker x := by
    simp [RingHom.mem_ker]
  rw [← hT] at hm
  obtain ⟨o, ho⟩ := key _ hm
  refine ⟨o, ?_⟩
  have : D a = D (a - algebraMap O R (x a)) := by
    conv_lhs => rw [← sub_add_cancel a (algebraMap O R (x a))]
    rw [hadd, halg, add_zero]
  rw [this, ho]

private def dualHom {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (x : R →ₐ[O] O) (d : R → O)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = x a * d b + d a * x b)
    (halg : ∀ o, d (algebraMap O R o) = 0) : R →ₐ[O] DualNumber O where
  toFun a := TrivSqZeroExt.inl (x a) + TrivSqZeroExt.inr (d a)
  map_one' := by
    have : d 1 = 0 := by simpa using halg 1
    ext <;> simp [this]
  map_mul' a b := by
    ext <;> simp [hmul, mul_comm]
  map_zero' := by
    have : d 0 = 0 := by simpa using halg 0
    ext <;> simp [this]
  map_add' a b := by
    ext <;> simp [hadd]
  commutes' o := by
    ext <;> simp [halg, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Take `⟨c, hc, h⟩` from `exists_den x D hadd hmul halg`. Use `choose d hd using h`. Establish `inj` using `IsFractionRing.injective O E`. Establish `hc' : algebraMap O E c ≠ 0` using `fun h => hc (inj (by rw [h, map_zero]))`. Use `hsep (dualHom x d (fun a b => inj (by rw [map_add, hd, hd, hd, hadd, mul_add])) (fun a b => inj (by rw [map_add, map_mul, map_mul, hd, hd, hd, hmul]; ring)) (fun o => inj (by rw [hd, halg, mul_zero, map_zero]))) (dualHom x (fun _ => 0) (by simp) (by simp) (by simp)) (fun s => by` as an intermediate fact.

Establish `: d (e s) = 0` using `inj (by rw [hd, hs, mul_zero, map_zero])`. Apply the tactic sequence `ext <;> simp [dualHom, this])`. Establish `h3 : d a = 0`. Simplify `congrArg TrivSqZeroExt.snd (DFunLike.congr_fun this a)` using `[dualHom]`. Establish `h4` using `hd a`.

Rewrite `h4` using `[h3, map_zero]`. Conclude with `(mul_eq_zero.mp h4.symm).resolve_left hc'`.
-/
private theorem der_zero {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R]
    [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (x : R →ₐ[O] O) (D : R → E)
    (hadd : ∀ a b, D (a + b) = D a + D b)
    (hmul : ∀ a b, D (a * b) = algebraMap O E (x a) * D b + D a * algebraMap O E (x b))
    (halg : ∀ o, D (algebraMap O R o) = 0) (S : Type) (e : S → R)
    (hsep : ∀ f f' : R →ₐ[O] DualNumber O, (∀ s, f (e s) = f' (e s)) → f = f')
    (hs : ∀ s, D (e s) = 0) (a : R) : D a = 0 := by
  obtain ⟨c, hc, h⟩ := exists_den x D hadd hmul halg
  choose d hd using h
  have inj := IsFractionRing.injective O E
  have hc' : algebraMap O E c ≠ 0 := fun h => hc (inj (by rw [h, map_zero]))
  have := hsep
    (dualHom x d (fun a b => inj (by rw [map_add, hd, hd, hd, hadd, mul_add]))
      (fun a b => inj (by rw [map_add, map_mul, map_mul, hd, hd, hd, hmul]; ring))
      (fun o => inj (by rw [hd, halg, mul_zero, map_zero])))
    (dualHom x (fun _ => 0) (by simp) (by simp) (by simp))
    (fun s => by
      have : d (e s) = 0 := inj (by rw [hd, hs, mul_zero, map_zero])
      ext <;> simp [dualHom, this])
  have h3 : d a = 0 := by
    simpa [dualHom] using congrArg TrivSqZeroExt.snd (DFunLike.congr_fun this a)
  have h4 := hd a
  rw [h3, map_zero] at h4
  exact (mul_eq_zero.mp h4.symm).resolve_left hc'

/- English proof (translation)
Introduce `O R E _ _ _ _ _ _ _ _ n I x φ S e h hsep`. Set `L : MvPowerSeries (Fin n) E →ₗ[E] (Fin n → E)` to `LinearMap.pi fun j => MvPowerSeries.coeff (Finsupp.single j 1)`. Establish `hL : ∀ f j, L f j = MvPowerSeries.coeff (Finsupp.single j 1) f` using `fun _ _ => rfl`. Establish `hLmul : ∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f`. Introduce `f g`.

Use function extensionality and compare the values at `j`. Simplify using `only [hL, coeff1_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hm2 : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2, L f = 0`. Establish `hm : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E), MvPowerSeries.constantCoeff f = 0`.

Introduce `f hf`. Assume the negation of the conclusion as `hne`. Conclude with `hf (MvPowerSeries.isUnit_iff_constantCoeff.mpr (Ne.isUnit hne))`. Introduce `f hf`. Rewrite `hf` using `[pow_two]`.

Use `Submodule.mul_induction_on hf ?_ ?_` and prove the remaining obligations. Introduce `a ha b hb`. Rewrite using `[hLmul, hm a ha, hm b hb]`. Simplify using the standard rewrite rules. Introduce `a b ha hb`.

Rewrite using `[map_add, ha, hb, add_zero]`. Establish `hspan : Submodule.span E (Set.range fun s => L (φ (e s))) = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨lam, hlam, hker⟩` from `Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)`. Establish `hD` using `der_zero x (fun a => lam (L (φ a))) (fun a b => by simp) (fun a b => by`.

Rewrite using `[map_mul, hLmul, h.const, h.const]`. Simplify using `only [map_add, map_smul, smul_eq_mul]`. Use the proof step `ring)`. Use the proof step `(fun o => by`. Establish `: L (φ (algebraMap O R o)) = 0`.

Use function extensionality and compare the values at `j`. Rewrite using `[AlgHom.commutes, hL, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]`. Simplify using the standard rewrite rules. Rewrite using `[this, map_zero])`. Use `S e hsep (fun s => hker (Submodule.subset_span ⟨s, rfl⟩))`.

Apply `hlam` to reduce the goal to its premises. Use `(Pi.basisFun E (Fin n)).ext fun j => ?_` and prove the remaining obligations. Take `⟨a, c, hc, hca⟩` from `h.dense 2 (MvPowerSeries.X j)`. Establish `h1` using `hm2 _ hca`. Establish `hX : L (MvPowerSeries.X j) = Pi.basisFun E (Fin n) j`.

Use function extensionality and compare the values at `i`. Rewrite using `[hL, MvPowerSeries.coeff_index_single_X]`. Simplify using `[Pi.single_apply]`. Rewrite `h1` using `[map_sub, ← algebraMap_smul E c, map_smul, hX, sub_eq_zero]`. Establish `h2` using `hD a`.

Simplify using `only [← h1, map_smul, smul_eq_mul] at h2`. Establish `hc' : algebraMap O E c ≠ 0` using `fun h => hc (IsFractionRing.injective O E (by rw [h, map_zero]))`. Conclude with `(mul_eq_zero.mp h2).resolve_left hc'`. Take `⟨b, hb, hbs, hbi⟩` from `exists_linearIndependent E (Set.range fun s => L (φ (e s)))`. Rewrite `hbs` using `[hspan]`.

Establish `hfin : b.Finite` using `hbi.set_finite_of_isNoetherian`. Use `haveI := hfin.fintype`. Set `B : Module.Basis b E (Fin n → E)` to `Module.Basis.mk hbi (by simp [hbs])`. Establish `hcard : Fintype.card b = n`. Rewrite using `[← Module.finrank_eq_card_basis B]`.

Simplify using the standard rewrite rules. Set `q : Fin n ≃ b` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `choose u hu using fun i : Fin n => hb (q i).2`. Use `⟨u, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff, ← hbs]`.

Use `Submodule.span_mono fun v hv => ⟨q.symm ⟨v, hv⟩, ?_⟩` and prove the remaining obligations. Use `hu (q.symm ⟨v, hv⟩)` as an intermediate fact. Rewrite `this` using `[Equiv.apply_symm_apply]`. Conclude with `this`.
-/
theorem UpperTheory.V.Loc.chartSpan :
    ∀ {O R E : Type} [CommRing O] [IsDomain O] [CommRing R] [IsNoetherianRing R] [Algebra O R] [Field E] [Algebra O E] [IsFractionRing O E] (n : ℕ) (I : Ideal R) (x : R →ₐ[O] O) (φ : R →ₐ[O] MvPowerSeries (Fin n) E) (S : Type) (e : S → R), UpperTheory.V.Loc.IsCompl I x φ → (∀ f f' : R →ₐ[O] DualNumber O, (∀ s, f (e s) = f' (e s)) → f = f') → ∃ u : Fin n → S, Submodule.span E (Set.range fun i j : Fin n => MvPowerSeries.coeff (Finsupp.single j 1) (φ (e (u i)))) = ⊤ := by
  intro O R E _ _ _ _ _ _ _ _ n I x φ S e h hsep
  classical
  let L : MvPowerSeries (Fin n) E →ₗ[E] (Fin n → E) :=
    LinearMap.pi fun j => MvPowerSeries.coeff (Finsupp.single j 1)
  have hL : ∀ f j, L f j = MvPowerSeries.coeff (Finsupp.single j 1) f := fun _ _ => rfl
  have hLmul : ∀ f g, L (f * g) = MvPowerSeries.constantCoeff f • L g + MvPowerSeries.constantCoeff g • L f := by
    intro f g
    funext j
    simp only [hL, coeff1_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hm2 : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E) ^ 2, L f = 0 := by
    have hm : ∀ f ∈ maximalIdeal (MvPowerSeries (Fin n) E), MvPowerSeries.constantCoeff f = 0 := by
      intro f hf
      by_contra hne
      exact hf (MvPowerSeries.isUnit_iff_constantCoeff.mpr (Ne.isUnit hne))
    intro f hf
    rw [pow_two] at hf
    refine Submodule.mul_induction_on hf ?_ ?_
    · intro a ha b hb
      rw [hLmul, hm a ha, hm b hb]; simp
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  have hspan : Submodule.span E (Set.range fun s => L (φ (e s))) = ⊤ := by
    by_contra hne
    obtain ⟨lam, hlam, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    have hD := der_zero x (fun a => lam (L (φ a))) (fun a b => by simp)
      (fun a b => by
        rw [map_mul, hLmul, h.const, h.const]
        simp only [map_add, map_smul, smul_eq_mul]
        ring)
      (fun o => by
        have : L (φ (algebraMap O R o)) = 0 := by
          funext j
          rw [AlgHom.commutes, hL, MvPowerSeries.algebraMap_apply, MvPowerSeries.coeff_C]
          simp
        rw [this, map_zero])
      S e hsep (fun s => hker (Submodule.subset_span ⟨s, rfl⟩))
    apply hlam
    refine (Pi.basisFun E (Fin n)).ext fun j => ?_
    obtain ⟨a, c, hc, hca⟩ := h.dense 2 (MvPowerSeries.X j)
    have h1 := hm2 _ hca
    have hX : L (MvPowerSeries.X j) = Pi.basisFun E (Fin n) j := by
      funext i
      rw [hL, MvPowerSeries.coeff_index_single_X]
      simp [Pi.single_apply]
    rw [map_sub, ← algebraMap_smul E c, map_smul, hX, sub_eq_zero] at h1
    have h2 := hD a
    simp only [← h1, map_smul, smul_eq_mul] at h2
    have hc' : algebraMap O E c ≠ 0 := fun h => hc (IsFractionRing.injective O E (by rw [h, map_zero]))
    exact (mul_eq_zero.mp h2).resolve_left hc'
  obtain ⟨b, hb, hbs, hbi⟩ := exists_linearIndependent E (Set.range fun s => L (φ (e s)))
  rw [hspan] at hbs
  have hfin : b.Finite := hbi.set_finite_of_isNoetherian
  haveI := hfin.fintype
  let B : Module.Basis b E (Fin n → E) := Module.Basis.mk hbi (by simp [hbs])
  have hcard : Fintype.card b = n := by
    rw [← Module.finrank_eq_card_basis B]; simp
  let q : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose u hu using fun i : Fin n => hb (q i).2
  refine ⟨u, ?_⟩
  rw [eq_top_iff, ← hbs]
  refine Submodule.span_mono fun v hv => ⟨q.symm ⟨v, hv⟩, ?_⟩
  have := hu (q.symm ⟨v, hv⟩)
  rw [Equiv.apply_symm_apply] at this
  exact this

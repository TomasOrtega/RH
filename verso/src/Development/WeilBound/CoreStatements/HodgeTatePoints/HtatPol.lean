import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveModuleModNBasis

noncomputable section

namespace PositivityTheory.HtPt.Htat

open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Use `set S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)`. Establish `hS : S ≤ nonZeroDivisors (𝓞 E)`. Introduce and unpack `_ ⟨n, hn, rfl⟩`. Conclude with `mem_nonZeroDivisors_of_ne_zero (by`. Simplify using `using (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)).ne (nonZeroDivisors.ne_zero hn))`.

Set `f` to `TensorProduct.mk (𝓞 E) E M 1`. Use `haveI hloc : IsLocalizedModule S f := (isLocalizedModule_iff_isBaseChange S E f).mpr (TensorProduct.isBaseChange (𝓞 E) M E)`. Use `haveI : IsLocalizedModule (nonZeroDivisors ℤ) (f.restrictScalars ℤ) := IsLocalizedModule.restrictScalars (nonZeroDivisors ℤ) f`. Establish `h1` using `IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (f.restrictScalars ℤ) le_rfl`. Establish `h2` using `IsLocalizedModule.finrank_eq S f hS`.

Establish `h3` using `IsLocalization.finrank_eq E S hS (N := TensorProduct (𝓞 E) E M)`. Establish `h4` using `IsFractionRing.finrank_right_eq ℤ ℚ (TensorProduct (𝓞 E) E M)`. Establish `h5` using `Module.finrank_mul_finrank ℚ E (TensorProduct (𝓞 E) E M)`. Rewrite using `[← h1, ← h4, ← h5, h3, h2, mul_comm]`.
-/
theorem finrank_int_eq {E : Type} [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M]
    [Module.Finite (𝓞 E) M] :
    Module.finrank ℤ M = Module.finrank (𝓞 E) M * Module.finrank ℚ E := by
  set S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)
  have hS : S ≤ nonZeroDivisors (𝓞 E) := by
    rintro _ ⟨n, hn, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero (by
      simpa using (FaithfulSMul.algebraMap_injective ℤ (𝓞 E)).ne (nonZeroDivisors.ne_zero hn))
  let f := TensorProduct.mk (𝓞 E) E M 1
  haveI hloc : IsLocalizedModule S f :=
    (isLocalizedModule_iff_isBaseChange S E f).mpr (TensorProduct.isBaseChange (𝓞 E) M E)
  haveI : IsLocalizedModule (nonZeroDivisors ℤ) (f.restrictScalars ℤ) :=
    IsLocalizedModule.restrictScalars (nonZeroDivisors ℤ) f
  have h1 := IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ) (f.restrictScalars ℤ) le_rfl
  have h2 := IsLocalizedModule.finrank_eq S f hS
  have h3 := IsLocalization.finrank_eq E S hS (N := TensorProduct (𝓞 E) E M)
  have h4 := IsFractionRing.finrank_right_eq ℤ ℚ (TensorProduct (𝓞 E) E M)
  have h5 := Module.finrank_mul_finrank ℚ E (TensorProduct (𝓞 E) E M)
  rw [← h1, ← h4, ← h5, h3, h2, mul_comm]

/- English proof (translation)
Set `Rp` to `Localization.AtPrime P`. Set `f` to `TensorProduct.mk R Rp M 1`. Use `haveI hloc : IsLocalizedModule P.primeCompl f := (isLocalizedModule_iff_isBaseChange P.primeCompl Rp f).mpr (TensorProduct.isBaseChange R M Rp)`. Establish `hle : P.primeCompl ≤ nonZeroDivisors R` using `fun s hs => mem_nonZeroDivisors_of_ne_zero (fun h => hs (h ▸ P.zero_mem))`. Establish `hrank : Module.finrank Rp (TensorProduct R Rp M) = Module.finrank R M` using `(IsLocalization.finrank_eq Rp P.primeCompl hle).trans (IsLocalizedModule.finrank_eq P.primeCompl f hle)`.

Use `haveI : Module.Free Rp (TensorProduct R Rp M) := Module.free_of_flat_of_isLocalRing`. Set `b` to `Module.finBasisOfFinrankEq Rp (TensorProduct R Rp M) hrank`. Use `choose ms hms using fun i => IsLocalizedModule.mk'_surjective P.primeCompl f (b i)`. Use `⟨fun i => (ms i).1, ?_⟩` and prove the remaining obligations. Use `set N := Submodule.span R (Set.range fun i => (ms i).1)`.

Establish `htop : Submodule.localized' Rp P.primeCompl f N = ⊤`. Rewrite using `[eq_top_iff, ← b.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `(Submodule.mem_localized' Rp P.primeCompl f N _).mpr ⟨(ms i).1, Submodule.subset_span ⟨i, rfl⟩, (ms i).2, hms i⟩`. Rewrite using `[eq_top_iff]`.

Introduce `x _`. Take `⟨y, hy, t, hyt⟩` from `(Submodule.mem_localized' Rp P.primeCompl f N (f x)).mp (htop ▸ Submodule.mem_top)`. Rewrite `hyt` using `[IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul]`. Take `⟨c, hc⟩` from `IsLocalizedModule.exists_of_eq (S := P.primeCompl) hyt`. Establish `hmem : ((c : R) * t) • x ∈ N`.

Rewrite using `[mul_smul, ← Submonoid.smul_def c, ← hc, Submonoid.smul_def]`. Conclude with `N.smul_mem _ hy`. Establish `hnot : (c : R) * t ∉ P` using `(P.primeCompl.mul_mem c.2 t.2)`. Take `⟨r, i, hi, hri⟩` from `hP.exists_inv hnot`. Establish `: x = (r * ((c : R) * t)) • x + i • x` using `by rw [← add_smul, hri, one_smul]`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (by rw [mul_smul]; exact N.smul_mem r hmem)) (Submodule.mem_sup_right (Submodule.smul_mem_smul hi Submodule.mem_top))`.
-/
private theorem exists_span_sup_maximal_smul_eq_top {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) [hP : P.IsMaximal]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ∃ m : Fin (Module.finrank R M) → M, Submodule.span R (Set.range m) ⊔ P • ⊤ = ⊤ := by
  classical
  let Rp := Localization.AtPrime P
  let f := TensorProduct.mk R Rp M 1
  haveI hloc : IsLocalizedModule P.primeCompl f :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl Rp f).mpr (TensorProduct.isBaseChange R M Rp)
  have hle : P.primeCompl ≤ nonZeroDivisors R := fun s hs =>
    mem_nonZeroDivisors_of_ne_zero (fun h => hs (h ▸ P.zero_mem))
  have hrank : Module.finrank Rp (TensorProduct R Rp M) = Module.finrank R M :=
    (IsLocalization.finrank_eq Rp P.primeCompl hle).trans (IsLocalizedModule.finrank_eq P.primeCompl f hle)
  haveI : Module.Free Rp (TensorProduct R Rp M) := Module.free_of_flat_of_isLocalRing
  let b := Module.finBasisOfFinrankEq Rp (TensorProduct R Rp M) hrank
  choose ms hms using fun i => IsLocalizedModule.mk'_surjective P.primeCompl f (b i)
  refine ⟨fun i => (ms i).1, ?_⟩
  set N := Submodule.span R (Set.range fun i => (ms i).1)
  have htop : Submodule.localized' Rp P.primeCompl f N = ⊤ := by
    rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (Submodule.mem_localized' Rp P.primeCompl f N _).mpr
      ⟨(ms i).1, Submodule.subset_span ⟨i, rfl⟩, (ms i).2, hms i⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, t, hyt⟩ := (Submodule.mem_localized' Rp P.primeCompl f N (f x)).mp (htop ▸ Submodule.mem_top)
  rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hyt
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) hyt
  have hmem : ((c : R) * t) • x ∈ N := by
    rw [mul_smul, ← Submonoid.smul_def c, ← hc, Submonoid.smul_def]
    exact N.smul_mem _ hy
  have hnot : (c : R) * t ∉ P := (P.primeCompl.mul_mem c.2 t.2)
  obtain ⟨r, i, hi, hri⟩ := hP.exists_inv hnot
  have : x = (r * ((c : R) * t)) • x + i • x := by rw [← add_smul, hri, one_smul]
  rw [this]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (by rw [mul_smul]; exact N.smul_mem r hmem))
    (Submodule.mem_sup_right (Submodule.smul_mem_smul hi Submodule.mem_top))

/- English proof (translation)
Substitute `hn` using the available equality. Use `set F := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).toFinset`. Establish `hprime : ∀ P ∈ F, Prime P` using `fun P hP => UniqueFactorizationMonoid.prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)`. Establish `hm : ∀ P ∈ F, ∃ m : Fin (Module.finrank R M) → M, Submodule.span R (Set.range m) ⊔ P • (⊤ : Submodule R M) = ⊤`. Introduce `P hP`.

Use `haveI : P.IsMaximal := Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime (hprime P hP)) (by rw [← Ideal.zero_eq_bot]; exact (hprime P hP).ne_zero)`. Conclude with `exists_span_sup_maximal_smul_eq_top P M`. Use `choose! m hm using hm`. Establish `he : ∀ Q ∈ F, ∃ e : R, ∀ P ∈ F, e - (if P = Q then 1 else 0) ∈ P`. Introduce `Q _`.

Take `⟨y, hy⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := F) id (fun _ => 1) (fun i hi => hprime i hi) (fun i _ j _ h => h) (fun P => if P.1 = Q then 1 else 0)`. Conclude with `⟨y, fun P hP => by simpa using hy P hP⟩`. Use `choose! e he using he`. Set `u : Fin (Module.finrank R M) → M` to `fun i => ∑ Q ∈ F, e Q • m Q i`. Establish `hdiff : ∀ P ∈ F, ∀ i, u i - m P i ∈ P • (⊤ : Submodule R M)`.

Introduce `P hP i`. Establish `: u i - m P i = ∑ Q ∈ F, (e Q - if P = Q then 1 else 0) • m Q i`. Simplify using `only [u, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, hP, if_true]`. Rewrite using `[this]`. Conclude with `Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem_smul (he Q hQ P hP) Submodule.mem_top`.

Use `set N := Submodule.span R (Set.range u) ⊔ Ideal.span {a} • (⊤ : Submodule R M)`. Establish `hcov : ∀ P ∈ F, N ⊔ P • (⊤ : Submodule R M) = ⊤`. Introduce `P hP`. Use `eq_top_iff.mpr ((hm P hP).symm.le.trans (sup_le ?_ le_sup_right))` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Establish `: m P i = u i - (u i - m P i)` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩))) (Submodule.mem_sup_right (hdiff P hP i))`. Establish `key : ∀ I J : Ideal R, N ⊔ I • (⊤ : Submodule R M) = ⊤ → N ⊔ J • (⊤ : Submodule R M) = ⊤ → N ⊔ (I * J) • (⊤ : Submodule R M) = ⊤`.

Introduce `I J hI hJ`. Use `eq_top_iff.mpr (hI.symm.le.trans (sup_le le_sup_left ?_))` and prove the remaining obligations. Rewrite using `[Submodule.mul_smul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hfac : ∀ s : Multiset (Ideal R), (∀ P ∈ s, P ∈ F) → N ⊔ s.prod • (⊤ : Submodule R M) = ⊤`.

Introduce `s`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => intro _`. Simplify using the standard rewrite rules. Consider the case `cons P s ih`.

Introduce `h`. Rewrite using `[Multiset.prod_cons]`. Conclude with `key _ _ (hcov P (h P (Multiset.mem_cons_self _ _))) (ih fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ))`. Establish `hN : N = ⊤`. Use `hfac (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})) (fun P hP => Multiset.mem_toFinset.mpr hP)` as an intermediate fact.

Rewrite `this` using `[Ideal.prod_normalizedFactors_eq_self (by simpa using ha), sup_eq_left.mpr le_sup_right]`. Then use the resulting hypothesis. Use `⟨u, fun x => ?_⟩` and prove the remaining obligations. Establish `hx : x ∈ N` using `hN ▸ Submodule.mem_top`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.mp hx`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).mp hy`.

Rewrite `hz` using `[Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]`. Take `⟨x', _, rfl⟩` from `hz`. Conclude with `⟨c, x', rfl⟩`.
-/
private theorem exists_finrank_family_mod_smul {R : Type} [CommRing R] [IsDedekindDomain R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (n : ℕ) (hn : Module.finrank R M = n) (a : R) (ha : a ≠ 0) :
    ∃ u : Fin n → M, ∀ x : M, ∃ (c : Fin n → R) (x' : M), x = ∑ i, c i • u i + a • x' := by
  classical
  subst hn
  set F := (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a})).toFinset
  have hprime : ∀ P ∈ F, Prime P := fun P hP =>
    UniqueFactorizationMonoid.prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)
  have hm : ∀ P ∈ F, ∃ m : Fin (Module.finrank R M) → M,
      Submodule.span R (Set.range m) ⊔ P • (⊤ : Submodule R M) = ⊤ := by
    intro P hP
    haveI : P.IsMaximal := Ideal.IsPrime.isMaximal (Ideal.isPrime_of_prime (hprime P hP))
      (by rw [← Ideal.zero_eq_bot]; exact (hprime P hP).ne_zero)
    exact exists_span_sup_maximal_smul_eq_top P M
  choose! m hm using hm
  have he : ∀ Q ∈ F, ∃ e : R, ∀ P ∈ F, e - (if P = Q then 1 else 0) ∈ P := by
    intro Q _
    obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := F) id (fun _ => 1)
      (fun i hi => hprime i hi) (fun i _ j _ h => h) (fun P => if P.1 = Q then 1 else 0)
    exact ⟨y, fun P hP => by simpa using hy P hP⟩
  choose! e he using he
  let u : Fin (Module.finrank R M) → M := fun i => ∑ Q ∈ F, e Q • m Q i
  have hdiff : ∀ P ∈ F, ∀ i, u i - m P i ∈ P • (⊤ : Submodule R M) := by
    intro P hP i
    have : u i - m P i = ∑ Q ∈ F, (e Q - if P = Q then 1 else 0) • m Q i := by
      simp only [u, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq, hP, if_true]
    rw [this]
    exact Submodule.sum_mem _ fun Q hQ => Submodule.smul_mem_smul (he Q hQ P hP) Submodule.mem_top
  set N := Submodule.span R (Set.range u) ⊔ Ideal.span {a} • (⊤ : Submodule R M)
  have hcov : ∀ P ∈ F, N ⊔ P • (⊤ : Submodule R M) = ⊤ := by
    intro P hP
    refine eq_top_iff.mpr ((hm P hP).symm.le.trans (sup_le ?_ le_sup_right))
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have : m P i = u i - (u i - m P i) := by abel
    rw [this]
    exact Submodule.sub_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)))
      (Submodule.mem_sup_right (hdiff P hP i))
  have key : ∀ I J : Ideal R, N ⊔ I • (⊤ : Submodule R M) = ⊤ → N ⊔ J • (⊤ : Submodule R M) = ⊤ →
      N ⊔ (I * J) • (⊤ : Submodule R M) = ⊤ := by
    intro I J hI hJ
    refine eq_top_iff.mpr (hI.symm.le.trans (sup_le le_sup_left ?_))
    rw [Submodule.mul_smul]
    calc I • (⊤ : Submodule R M) = I • (N ⊔ J • ⊤) := by rw [hJ]
      _ = I • N ⊔ I • J • ⊤ := Submodule.smul_sup _ _ _
      _ ≤ N ⊔ I • J • ⊤ := sup_le_sup_right (Submodule.smul_le_right) _
  have hfac : ∀ s : Multiset (Ideal R), (∀ P ∈ s, P ∈ F) → N ⊔ s.prod • (⊤ : Submodule R M) = ⊤ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons P s ih =>
      intro h
      rw [Multiset.prod_cons]
      exact key _ _ (hcov P (h P (Multiset.mem_cons_self _ _)))
        (ih fun Q hQ => h Q (Multiset.mem_cons_of_mem hQ))
  have hN : N = ⊤ := by
    have := hfac (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {a}))
      (fun P hP => Multiset.mem_toFinset.mpr hP)
    rwa [Ideal.prod_normalizedFactors_eq_self (by simpa using ha), sup_eq_left.mpr le_sup_right] at this
  refine ⟨u, fun x => ?_⟩
  have hx : x ∈ N := hN ▸ Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hy
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hz
  obtain ⟨x', _, rfl⟩ := hz
  exact ⟨c, x', rfl⟩

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor in
/- English proof (translation)
Introduce `E _ _ _ H D p _`. Use `haveI := D.fin`. Use `haveI := D.proj`. Establish `hfinZ : Module.Finite ℤ D.La` using `Module.Finite.trans (𝓞 E) D.La`. Use `haveI : Module.IsTorsionFree (𝓞 E) D.La := inferInstance`.

Use `haveI : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans (𝓞 E)`. Take `⟨u, hu⟩` from `exists_finrank_family_mod_smul D.La (D.p + D.q) D.rank (p : 𝓞 E) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)`. Use `⟨u, ⟨inferInstance, hfinZ, D.alt, D.unimod, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `a x y`. Rewrite using `[D.adj]`.

Use `congr 2`. Use `ext`. Simplify using `[H.bar_eq]`. Rewrite using `[finrank_int_eq (E := E), D.rank]`. Introduce `x`.

Take `⟨a, x', hx⟩` from `hu x`. Conclude with `⟨a, x', by rw [hx, Nat.cast_smul_eq_nsmul]⟩`.
-/
theorem pol_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (p : ℕ) [Fact p.Prime], ∃ u : Fin (D.p + D.q) → D.La, IsPolLattice (IsCMField.complexConj E).toRingEquiv p D.EF u := by
  intro E _ _ _ H D p _
  haveI := D.fin
  haveI := D.proj
  have hfinZ : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : Module.IsTorsionFree (𝓞 E) D.La := inferInstance
  haveI : Module.IsTorsionFree ℤ D.La := Module.IsTorsionFree.trans (𝓞 E)
  obtain ⟨u, hu⟩ := exists_finrank_family_mod_smul D.La (D.p + D.q) D.rank (p : 𝓞 E)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  refine ⟨u, ⟨inferInstance, hfinZ, D.alt, D.unimod, ?_, ?_, ?_⟩⟩
  · intro a x y
    rw [D.adj]
    congr 2
    ext
    simp [H.bar_eq]
  · rw [finrank_int_eq (E := E), D.rank]
  · intro x
    obtain ⟨a, x', hx⟩ := hu x
    exact ⟨a, x', by rw [hx, Nat.cast_smul_eq_nsmul]⟩

end PositivityTheory.HtPt.Htat

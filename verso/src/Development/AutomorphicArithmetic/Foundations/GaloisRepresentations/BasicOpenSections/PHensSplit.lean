import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.ResClosed
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open UpperTheory.Gal.TranscendenceTraces (gp pt Wt fib IsWt nwt LocNml)
open UpperTheory.Gal.crystallineComparison (resPt twist PtId)
open UpperTheory.Gal UpperTheory.Gal.Mod

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `F hF hdeg`. Use `⟨0, ?_⟩` and prove the remaining obligations.

Simplify using `only [Multiset.map_zero, Multiset.prod_zero]`. Conclude with `Polynomial.eq_one_of_monic_natDegree_zero hF hdeg`. Consider the case `succ n ih`. Introduce `F hF hdeg`. Establish `hm : (F.map (algebraMap V (FractionRing V))).Monic` using `hF.map _`.

Establish `hnd : (F.map (algebraMap V (FractionRing V))).natDegree = n + 1`. Rewrite using `[hF.natDegree_map, hdeg]`. Establish `hd0 : (F.map (algebraMap V (FractionRing V))).degree ≠ 0`. Introduce `h`. Rewrite `h` using `[Polynomial.degree_eq_natDegree hm.ne_zero, hnd]`.

Normalize the coercions in `at h`. Take `⟨x, hx⟩` from `IsAlgClosed.exists_root _ hd0`. Establish `hint : IsIntegral V x` using `⟨F, hF, by rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx⟩`. Take `⟨α, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Establish `hroot : F.IsRoot α`.

Apply `IsFractionRing.injective V (FractionRing V)` to reduce the goal to its premises. Rewrite `hx` using `[Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply]`. Rewrite using `[hx, map_zero]`. Establish `hmul : (Polynomial.X - Polynomial.C α) * (F /ₘ (Polynomial.X - Polynomial.C α)) = F` using `Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot`. Establish `hGm : (F /ₘ (Polynomial.X - Polynomial.C α)).Monic` using `Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C α) (by rw [hmul]; exact hF)`.

Establish `hGd : (F /ₘ (Polynomial.X - Polynomial.C α)).natDegree = n`. Rewrite using `[Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C α), hdeg, Polynomial.natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers. Take `⟨s, hs⟩` from `ih _ hGm hGd`. Use `⟨α ::ₘ s, ?_⟩` and prove the remaining obligations.

Rewrite using `[Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]`.
-/
private theorem split_monic (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [IsAlgClosed (FractionRing V)] :
    ∀ (n : ℕ) (F : Polynomial V), F.Monic → F.natDegree = n →
      ∃ s : Multiset V, F = (s.map fun α => Polynomial.X - Polynomial.C α).prod := by
  intro n
  induction n with
  | zero =>
    intro F hF hdeg
    refine ⟨0, ?_⟩
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact Polynomial.eq_one_of_monic_natDegree_zero hF hdeg
  | succ n ih =>
    intro F hF hdeg
    have hm : (F.map (algebraMap V (FractionRing V))).Monic := hF.map _
    have hnd : (F.map (algebraMap V (FractionRing V))).natDegree = n + 1 := by
      rw [hF.natDegree_map, hdeg]
    have hd0 : (F.map (algebraMap V (FractionRing V))).degree ≠ 0 := by
      intro h
      rw [Polynomial.degree_eq_natDegree hm.ne_zero, hnd] at h
      norm_cast at h
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd0
    have hint : IsIntegral V x := ⟨F, hF, by rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx⟩
    obtain ⟨α, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    have hroot : F.IsRoot α := by
      apply IsFractionRing.injective V (FractionRing V)
      rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply] at hx
      rw [hx, map_zero]
    have hmul : (Polynomial.X - Polynomial.C α) * (F /ₘ (Polynomial.X - Polynomial.C α)) = F :=
      Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
    have hGm : (F /ₘ (Polynomial.X - Polynomial.C α)).Monic :=
      Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C α) (by rw [hmul]; exact hF)
    have hGd : (F /ₘ (Polynomial.X - Polynomial.C α)).natDegree = n := by
      rw [Polynomial.natDegree_divByMonic _ (Polynomial.monic_X_sub_C α), hdeg,
        Polynomial.natDegree_X_sub_C]
      omega
    obtain ⟨s, hs⟩ := ih _ hGm hGd
    refine ⟨α ::ₘ s, ?_⟩
    rw [Multiset.map_cons, Multiset.prod_cons, ← hs, hmul]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty`. Simplify using `only [Multiset.map_zero, Multiset.prod_zero]`. Conclude with `isCoprime_one_left`. Consider the case `cons a t ih`.

Rewrite using `[Multiset.map_cons, Multiset.prod_cons]`. Conclude with `(h a (Multiset.mem_cons_self a t)).mul_left (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))`.
-/
private theorem coprime_left {R ι : Type} [CommRing R] (s : Multiset ι) (f : ι → R) (x : R)
    (h : ∀ a ∈ s, IsCoprime (f a) x) : IsCoprime (s.map f).prod x := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    exact isCoprime_one_left
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact (h a (Multiset.mem_cons_self a t)).mul_left (ih fun b hb => h b (Multiset.mem_cons_of_mem hb))

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty`. Introduce `h1`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using h1))`. Consider the case `cons a t ih`.

Rewrite using `[Multiset.map_cons, Multiset.prod_cons]`. Introduce `hm`. Break down `hP.mem_or_mem hm with h1 | h1` into its components or cases. Conclude with `h a (Multiset.mem_cons_self a t) h1`. Conclude with `ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)) h1`.
-/
private theorem prod_notMem {R ι : Type} [CommRing R] (P : Ideal R) [hP : P.IsPrime]
    (s : Multiset ι) (f : ι → R) (h : ∀ a ∈ s, f a ∉ P) : (s.map f).prod ∉ P := by
  induction s using Multiset.induction_on with
  | empty =>
    intro h1
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using h1))
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    intro hm
    rcases hP.mem_or_mem hm with h1 | h1
    · exact h a (Multiset.mem_cons_self a t) h1
    · exact ih (fun b hb => h b (Multiset.mem_cons_of_mem hb)) h1

/- English proof (translation)
Establish `hc : (m'.comap (algebraMap V A)).IsMaximal` using `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m'`. Rewrite `hv` using `[← IsLocalRing.eq_maximalIdeal hc]`. Conclude with `hv`.
-/
private theorem algebraMap_mem_maximal_of_mem_maximalIdeal (V : Type) [CommRing V] [IsLocalRing V] {A : Type} [CommRing A]
    [Algebra V A] [Algebra.IsIntegral V A] (m' : Ideal A) [m'.IsMaximal] {v : V}
    (hv : v ∈ IsLocalRing.maximalIdeal V) : algebraMap V A v ∈ m' := by
  have hc : (m'.comap (algebraMap V A)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m'
  rw [← IsLocalRing.eq_maximalIdeal hc] at hv
  exact hv

/- English proof (translation)
Take `⟨F, hF, hFa⟩` from `Algebra.IsIntegral.isIntegral (R := V) a`. Take `⟨s, hs⟩` from `split_monic V F.natDegree F hF rfl`. Use `set f : V → A := fun α => a - algebraMap V A α with hf`. Establish `hprod : (s.map f).prod = 0`. Establish `h0 : Polynomial.aeval a F = 0`.

Rewrite using `[Polynomial.aeval_def]`. Conclude with `hFa`. Rewrite `h0` using `[hs, map_multiset_prod, Multiset.map_map]`. Simplify `h0` using `[f, Function.comp_def]`. Use `set g := ((s.filter (fun α => f α ∈ m)).map f).prod with hg`.

Use `set h := ((s.filter (fun α => ¬ f α ∈ m)).map f).prod with hh`. Establish `hgh : g * h = 0`. Rewrite using `[hg, hh, ← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not, hprod]`. Establish `hhm : h ∉ m` using `prod_notMem m _ f (fun α hα => (Multiset.mem_filter.mp hα).2)`. Establish `hgm : g ∈ m`.

Establish `hz : g * h ∈ m`. Rewrite using `[hgh]`. Conclude with `m.zero_mem`. Conclude with `(hm.isPrime.mem_or_mem hz).resolve_right hhm`. Establish `hcop : IsCoprime g h`.

Apply `IsCoprime.symm` to reduce the goal to its premises. Apply `coprime_left` to reduce the goal to its premises. Introduce `β hβ`. Apply `IsCoprime.symm` to reduce the goal to its premises. Apply `coprime_left` to reduce the goal to its premises.

Introduce `α hα`. Establish `hPα : f α ∈ m` using `(Multiset.mem_filter.mp hα).2`. Establish `hPβ : f β ∉ m` using `(Multiset.mem_filter.mp hβ).2`. Establish `hu : IsUnit (α - β)`. Assume the negation of the conclusion as `hnu`.

Apply `hPβ` to reduce the goal to its premises. Establish `hmem : algebraMap V A (α - β) ∈ m` using `algebraMap_mem_maximal_of_mem_maximalIdeal V m ((IsLocalRing.mem_maximalIdeal _).mpr hnu)`. Establish `hfe : f β = f α + algebraMap V A (α - β)`. Simplify using `only [f, map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hfe]`. Conclude with `m.add_mem hPα hmem`. Take `⟨w, hw⟩` from `hu`. Use `⟨-algebraMap V A (↑w⁻¹ : V), algebraMap V A (↑w⁻¹ : V), ?_⟩` and prove the remaining obligations. Establish `hw1 : algebraMap V A (↑w⁻¹ : V) * algebraMap V A (α - β) = 1`.

Rewrite using `[← map_mul, ← hw, Units.inv_mul, map_one]`. Simplify using `only [f, map_sub] at hw1 ⊢`. Take the linear combination `hw1`. Take `⟨u, v, huv⟩` from `hcop`. Use `⟨v * h, ?_, ?_, ?_⟩` and prove the remaining obligations.

Use `show v * h * (v * h) = v * h`. Take the linear combination `(v * h) * huv - (u * v) * hgh`. Introduce `he`. Apply `hm.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← huv]`.

Conclude with `m.add_mem (m.mul_mem_left u hgm) he`. Introduce `m' hm' he`. Establish `hhm' : h ∉ m'` using `fun hh' => he (m'.mul_mem_left v hh')`. Establish `hex : ∃ α ∈ s, f α ∈ m'`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Establish `hn` using `prod_notMem (hP := hm'.isPrime) m' s f hne`. Rewrite `hn` using `[hprod]`. Conclude with `hn m'.zero_mem`. Take `⟨α, hαs, hαm'⟩` from `hex`.

Distinguish the cases in `hPα : f α ∈ m`. Conclude with `⟨α, hPα, hαm'⟩`. It suffices to derive a contradiction. Apply `hhm'` to reduce the goal to its premises. Establish `hmemf : α ∈ s.filter (fun α => ¬ f α ∈ m)` using `Multiset.mem_filter.mpr ⟨hαs, hPα⟩`.

Take `⟨c, hc⟩` from `Multiset.dvd_prod (Multiset.mem_map_of_mem f hmemf)`. Rewrite using `[hh, hc]`. Conclude with `m'.mul_mem_right c hαm'`.
-/
private theorem exists_idempotent_approx_at_maximal (V : Type) [CommRing V] [IsDomain V] [ValuationRing V]
    [IsAlgClosed (FractionRing V)] {A : Type} [CommRing A] [Algebra V A] [Algebra.IsIntegral V A]
    (m : Ideal A) [hm : m.IsMaximal] (a : A) :
    ∃ e : A, IsIdempotentElem e ∧ e ∉ m ∧ ∀ m' : Ideal A, m'.IsMaximal → e ∉ m' →
      ∃ β : V, a - algebraMap V A β ∈ m ∧ a - algebraMap V A β ∈ m' := by
  classical
  obtain ⟨F, hF, hFa⟩ := Algebra.IsIntegral.isIntegral (R := V) a
  obtain ⟨s, hs⟩ := split_monic V F.natDegree F hF rfl
  set f : V → A := fun α => a - algebraMap V A α with hf
  have hprod : (s.map f).prod = 0 := by
    have h0 : Polynomial.aeval a F = 0 := by
      rw [Polynomial.aeval_def]
      exact hFa
    rw [hs, map_multiset_prod, Multiset.map_map] at h0
    simpa [f, Function.comp_def] using h0
  set g := ((s.filter (fun α => f α ∈ m)).map f).prod with hg
  set h := ((s.filter (fun α => ¬ f α ∈ m)).map f).prod with hh
  have hgh : g * h = 0 := by
    rw [hg, hh, ← Multiset.prod_add, ← Multiset.map_add, Multiset.filter_add_not, hprod]
  have hhm : h ∉ m := prod_notMem m _ f (fun α hα => (Multiset.mem_filter.mp hα).2)
  have hgm : g ∈ m := by
    have hz : g * h ∈ m := by
      rw [hgh]
      exact m.zero_mem
    exact (hm.isPrime.mem_or_mem hz).resolve_right hhm
  have hcop : IsCoprime g h := by
    apply IsCoprime.symm
    apply coprime_left
    intro β hβ
    apply IsCoprime.symm
    apply coprime_left
    intro α hα
    have hPα : f α ∈ m := (Multiset.mem_filter.mp hα).2
    have hPβ : f β ∉ m := (Multiset.mem_filter.mp hβ).2
    have hu : IsUnit (α - β) := by
      by_contra hnu
      apply hPβ
      have hmem : algebraMap V A (α - β) ∈ m :=
        algebraMap_mem_maximal_of_mem_maximalIdeal V m ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
      have hfe : f β = f α + algebraMap V A (α - β) := by
        simp only [f, map_sub]
        ring
      rw [hfe]
      exact m.add_mem hPα hmem
    obtain ⟨w, hw⟩ := hu
    refine ⟨-algebraMap V A (↑w⁻¹ : V), algebraMap V A (↑w⁻¹ : V), ?_⟩
    have hw1 : algebraMap V A (↑w⁻¹ : V) * algebraMap V A (α - β) = 1 := by
      rw [← map_mul, ← hw, Units.inv_mul, map_one]
    simp only [f, map_sub] at hw1 ⊢
    linear_combination hw1
  obtain ⟨u, v, huv⟩ := hcop
  refine ⟨v * h, ?_, ?_, ?_⟩
  · show v * h * (v * h) = v * h
    linear_combination (v * h) * huv - (u * v) * hgh
  · intro he
    apply hm.ne_top
    rw [Ideal.eq_top_iff_one, ← huv]
    exact m.add_mem (m.mul_mem_left u hgm) he
  · intro m' hm' he
    have hhm' : h ∉ m' := fun hh' => he (m'.mul_mem_left v hh')
    have hex : ∃ α ∈ s, f α ∈ m' := by
      by_contra hne
      push_neg at hne
      have hn := prod_notMem (hP := hm'.isPrime) m' s f hne
      rw [hprod] at hn
      exact hn m'.zero_mem
    obtain ⟨α, hαs, hαm'⟩ := hex
    by_cases hPα : f α ∈ m
    · exact ⟨α, hPα, hαm'⟩
    · exfalso
      apply hhm'
      have hmemf : α ∈ s.filter (fun α => ¬ f α ∈ m) := Multiset.mem_filter.mpr ⟨hαs, hPα⟩
      obtain ⟨c, hc⟩ := Multiset.dvd_prod (Multiset.mem_map_of_mem f hmemf)
      rw [hh, hc]
      exact m'.mul_mem_right c hαm'

/- English proof (translation)
Introduce `V _ _ _ _ A _ _ _ m hm`. Take `⟨T, hT⟩` from `Module.Finite.fg_top (R := V) (M := A)`. Use `choose E hEi hEm hEm' using fun t : A => exists_idempotent_approx_at_maximal V m t`. Use `⟨∏ t ∈ T, E t, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show (∏ t ∈ T, E t) * (∏ t ∈ T, E t) = ∏ t ∈ T, E t`.

Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl (fun t _ => (hEi t).eq)`. Rewrite using `[Finset.prod_eq_multiset_prod]`. Conclude with `prod_notMem m T.val E (fun t _ => hEm t)`. Introduce `m' hm' hne`.

Assume the negation of the conclusion as `hem'`. Establish `hall : ∀ t ∈ T, ∃ β : V, t - algebraMap V A β ∈ m ⊓ m'`. Introduce `t ht`. Establish `hEt : E t ∉ m'`. Introduce `hE`.

Apply `hem'` to reduce the goal to its premises. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem E ht`. Rewrite using `[hc]`. Conclude with `m'.mul_mem_right c hE`. Take `⟨β, h1, h2⟩` from `hEm' t m' hm' hEt`.

Conclude with `⟨β, Ideal.mem_inf.mpr ⟨h1, h2⟩⟩`. Establish `hspan : ∀ x : A, ∃ β : V, x - algebraMap V A β ∈ m ⊓ m'`. Introduce `x`. Establish `hx : x ∈ Submodule.span V (T : Set A)`. Rewrite using `[hT]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy => exact hall y hy`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨β, hβ⟩` from `hy`. Take `⟨γ, hγ⟩` from `hz`. Use `⟨β + γ, ?_⟩` and prove the remaining obligations. Establish `hyz : y + z - algebraMap V A (β + γ) = (y - algebraMap V A β) + (z - algebraMap V A γ)`. Rewrite using `[map_add]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hyz]`. Conclude with `(m ⊓ m').add_mem hβ hγ`. Consider the case `smul c y _ hy`. Take `⟨β, hβ⟩` from `hy`.

Use `⟨c * β, ?_⟩` and prove the remaining obligations. Establish `hcy : c • y - algebraMap V A (c * β) = algebraMap V A c * (y - algebraMap V A β)`. Rewrite using `[Algebra.smul_def, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hcy]`.

Conclude with `(m ⊓ m').mul_mem_left _ hβ`. Establish `hle : m ≤ m'`. Introduce `x hx`. Take `⟨β, hβ⟩` from `hspan x`. Establish `hβ1` using `(Ideal.mem_inf.mp hβ).1`.

Establish `hβ2` using `(Ideal.mem_inf.mp hβ).2`. Establish `hβm : algebraMap V A β ∈ m`. Establish `hd` using `m.sub_mem hx hβ1`. Simplify using `using hd`. Establish `hβmax : β ∈ IsLocalRing.maximalIdeal V`.

Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]`. Introduce `hu`. Conclude with `hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hβm (hu.map _))`. Establish `hs` using `m'.add_mem hβ2 (algebraMap_mem_maximal_of_mem_maximalIdeal V m' hβmax)`. Simplify using `using hs`.

Conclude with `hne (hm.eq_of_le hm'.ne_top hle).symm`.
-/
theorem UpperTheory.Gal.Mod.hensSplit :
    HensSplit := by
  intro V _ _ _ _ A _ _ _ m hm
  classical
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := V) (M := A)
  choose E hEi hEm hEm' using fun t : A => exists_idempotent_approx_at_maximal V m t
  refine ⟨∏ t ∈ T, E t, ?_, ?_, ?_⟩
  · show (∏ t ∈ T, E t) * (∏ t ∈ T, E t) = ∏ t ∈ T, E t
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun t _ => (hEi t).eq)
  · rw [Finset.prod_eq_multiset_prod]
    exact prod_notMem m T.val E (fun t _ => hEm t)
  · intro m' hm' hne
    by_contra hem'
    have hall : ∀ t ∈ T, ∃ β : V, t - algebraMap V A β ∈ m ⊓ m' := by
      intro t ht
      have hEt : E t ∉ m' := by
        intro hE
        apply hem'
        obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem E ht
        rw [hc]
        exact m'.mul_mem_right c hE
      obtain ⟨β, h1, h2⟩ := hEm' t m' hm' hEt
      exact ⟨β, Ideal.mem_inf.mpr ⟨h1, h2⟩⟩
    have hspan : ∀ x : A, ∃ β : V, x - algebraMap V A β ∈ m ⊓ m' := by
      intro x
      have hx : x ∈ Submodule.span V (T : Set A) := by
        rw [hT]
        trivial
      induction hx using Submodule.span_induction with
      | mem y hy => exact hall y hy
      | zero => exact ⟨0, by simp⟩
      | add y z _ _ hy hz =>
        obtain ⟨β, hβ⟩ := hy
        obtain ⟨γ, hγ⟩ := hz
        refine ⟨β + γ, ?_⟩
        have hyz : y + z - algebraMap V A (β + γ) =
            (y - algebraMap V A β) + (z - algebraMap V A γ) := by
          rw [map_add]
          ring
        rw [hyz]
        exact (m ⊓ m').add_mem hβ hγ
      | smul c y _ hy =>
        obtain ⟨β, hβ⟩ := hy
        refine ⟨c * β, ?_⟩
        have hcy : c • y - algebraMap V A (c * β) = algebraMap V A c * (y - algebraMap V A β) := by
          rw [Algebra.smul_def, map_mul]
          ring
        rw [hcy]
        exact (m ⊓ m').mul_mem_left _ hβ
    have hle : m ≤ m' := by
      intro x hx
      obtain ⟨β, hβ⟩ := hspan x
      have hβ1 := (Ideal.mem_inf.mp hβ).1
      have hβ2 := (Ideal.mem_inf.mp hβ).2
      have hβm : algebraMap V A β ∈ m := by
        have hd := m.sub_mem hx hβ1
        simpa using hd
      have hβmax : β ∈ IsLocalRing.maximalIdeal V := by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
        intro hu
        exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hβm (hu.map _))
      have hs := m'.add_mem hβ2 (algebraMap_mem_maximal_of_mem_maximalIdeal V m' hβmax)
      simpa using hs
    exact hne (hm.eq_of_le hm'.ne_top hle).symm

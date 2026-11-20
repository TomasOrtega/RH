import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.FrobeniusSections.FieldGen

noncomputable section

namespace PositivityTheory.RgUd.TP.Desc.Piece.PSect

open Module Polynomial

/- English proof (translation)
Set `G : (Fin n → ℕ) → R` to `fun e => ∏ i, L i ^ e i`. Set `Φ : ((Fin n → Fin q) → T) →ₗ[k] R` to `∑ e : Fin n → Fin q, (LinearMap.mulRight k (G fun i => (e i : ℕ))) ∘ₗ T.val.toLinearMap ∘ₗ LinearMap.proj e`. Establish `hΦ : ∀ f, Φ f = ∑ e : Fin n → Fin q, (f e : R) * G (fun i => (e i : ℕ))`. Introduce `f`. Simplify using `[Φ, LinearMap.sum_apply]`.

Establish `hsingle : ∀ t ∈ T, ∀ e : Fin n → Fin q, t * G (fun i => (e i : ℕ)) ∈ LinearMap.range Φ`. Introduce `t ht e`. Use `⟨Pi.single e ⟨t, ht⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hΦ, Finset.sum_eq_single e]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules. Establish `hA : ∀ t ∈ T, ∀ e : Fin n → ℕ, t * G e ∈ LinearMap.range Φ`. Introduce `t ht e`.

Establish `hG : G e = (∏ i, (L i ^ q) ^ (e i / q)) * G (fun i => ((⟨e i % q, Nat.mod_lt _ hq⟩ : Fin q) : ℕ))`. Simplify using `only [G]`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← pow_mul, ← pow_add, Nat.div_add_mod]`.

Rewrite using `[hG, ← mul_assoc]`. Conclude with `hsingle _ (T.mul_mem ht (T.prod_mem fun i _ => T.pow_mem (hL i) _)) _`. Establish `hLmul : ∀ i e, L i * G e = G (e + Pi.single i 1)`. Introduce `i e`. Simplify using `only [G, Pi.add_apply, pow_add, Finset.prod_mul_distrib]`.

Rewrite using `[mul_comm]`. Use `congr 1`. Rewrite using `[Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]`. Simplify using the standard rewrite rules. Establish `hclosed : ∀ y ∈ Algebra.adjoin k ((T : Set R) ∪ Set.range L), ∀ m ∈ LinearMap.range Φ, y * m ∈ LinearMap.range Φ`.

Introduce `y hy`. Proceed by induction on `hy using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Introduce and unpack `m ⟨f, rfl⟩`. Rewrite using `[hΦ, Finset.mul_sum]`.

Use `Submodule.sum_mem _ fun e _ => ?_` and prove the remaining obligations. Break down `hx with hx | ⟨i, rfl⟩` into its components or cases. Rewrite using `[← mul_assoc]`. Conclude with `hsingle _ (T.mul_mem hx (f e).2) e`. Rewrite using `[mul_left_comm, hLmul]`.

Conclude with `hA _ (f e).2 _`. Consider the case `algebraMap a`. Introduce `m hm`. Rewrite using `[← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ a hm`.

Consider the case `add x y _ _ hx hy`. Introduce `m hm`. Rewrite using `[add_mul]`. Conclude with `add_mem (hx m hm) (hy m hm)`. Consider the case `mul x y _ _ hx hy`.

Introduce `m hm`. Rewrite using `[mul_assoc]`. Conclude with `hx _ (hy m hm)`. Establish `h1 : (1 : R) ∈ LinearMap.range Φ`. Use `hA 1 T.one_mem 0` as an intermediate fact.

Simplify `this` using `[G]`. Establish `hle : Subalgebra.toSubmodule (Algebra.adjoin k ((T : Set R) ∪ Set.range L)) ≤ LinearMap.range Φ`. Introduce `y hy`. Simplify using `using hclosed y hy 1 h1`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem finrank_adjoin_pow_le {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    [FiniteDimensional k R] (T : Subalgebra k R) (q n : ℕ) (hq : 0 < q) (L : Fin n → R)
    (hL : ∀ i, L i ^ q ∈ T) :
    finrank k (Algebra.adjoin k ((T : Set R) ∪ Set.range L)) ≤ q ^ n * finrank k T := by
  classical
  let G : (Fin n → ℕ) → R := fun e => ∏ i, L i ^ e i
  let Φ : ((Fin n → Fin q) → T) →ₗ[k] R :=
    ∑ e : Fin n → Fin q, (LinearMap.mulRight k (G fun i => (e i : ℕ))) ∘ₗ T.val.toLinearMap ∘ₗ
      LinearMap.proj e
  have hΦ : ∀ f, Φ f = ∑ e : Fin n → Fin q, (f e : R) * G (fun i => (e i : ℕ)) := by
    intro f; simp [Φ, LinearMap.sum_apply]
  have hsingle : ∀ t ∈ T, ∀ e : Fin n → Fin q, t * G (fun i => (e i : ℕ)) ∈ LinearMap.range Φ := by
    intro t ht e
    refine ⟨Pi.single e ⟨t, ht⟩, ?_⟩
    rw [hΦ, Finset.sum_eq_single e]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hA : ∀ t ∈ T, ∀ e : Fin n → ℕ, t * G e ∈ LinearMap.range Φ := by
    intro t ht e
    have hG : G e = (∏ i, (L i ^ q) ^ (e i / q)) *
        G (fun i => ((⟨e i % q, Nat.mod_lt _ hq⟩ : Fin q) : ℕ)) := by
      simp only [G]
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hG, ← mul_assoc]
    exact hsingle _ (T.mul_mem ht (T.prod_mem fun i _ => T.pow_mem (hL i) _)) _
  have hLmul : ∀ i e, L i * G e = G (e + Pi.single i 1) := by
    intro i e
    simp only [G, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    rw [mul_comm]
    congr 1
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  have hclosed : ∀ y ∈ Algebra.adjoin k ((T : Set R) ∪ Set.range L),
      ∀ m ∈ LinearMap.range Φ, y * m ∈ LinearMap.range Φ := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rintro m ⟨f, rfl⟩
      rw [hΦ, Finset.mul_sum]
      refine Submodule.sum_mem _ fun e _ => ?_
      rcases hx with hx | ⟨i, rfl⟩
      · rw [← mul_assoc]; exact hsingle _ (T.mul_mem hx (f e).2) e
      · rw [mul_left_comm, hLmul]; exact hA _ (f e).2 _
    | algebraMap a =>
      intro m hm; rw [← Algebra.smul_def]; exact Submodule.smul_mem _ a hm
    | add x y _ _ hx hy =>
      intro m hm; rw [add_mul]; exact add_mem (hx m hm) (hy m hm)
    | mul x y _ _ hx hy =>
      intro m hm; rw [mul_assoc]; exact hx _ (hy m hm)
  have h1 : (1 : R) ∈ LinearMap.range Φ := by
    have := hA 1 T.one_mem 0
    simpa [G] using this
  have hle : Subalgebra.toSubmodule (Algebra.adjoin k ((T : Set R) ∪ Set.range L)) ≤
      LinearMap.range Φ := by
    intro y hy
    simpa using hclosed y hy 1 h1
  calc finrank k (Algebra.adjoin k ((T : Set R) ∪ Set.range L))
      = finrank k (Subalgebra.toSubmodule (Algebra.adjoin k ((T : Set R) ∪ Set.range L))) :=
        (Subalgebra.finrank_toSubmodule _).symm
    _ ≤ finrank k (LinearMap.range Φ) := Submodule.finrank_mono hle
    _ ≤ finrank k ((Fin n → Fin q) → T) := LinearMap.finrank_range_le Φ
    _ = q ^ n * finrank k T := by simp [Module.finrank_pi_fintype]

/- English proof (translation)
Break down `Nat.eq_zero_or_pos c with rfl | hc` into its components or cases. Use `⟨⊤, fun s _ hs => by simpa using hnil s hs, fun r => ⟨r, Algebra.mem_top, by simp⟩⟩` and prove the remaining obligations. Establish `hq2 : 2 ≤ p ^ c` using `le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow hc.ne' p)`. Establish `hq0 : 0 < p ^ c` using `by omega`. Use `haveI : IsArtinianRing R := IsArtinianRing.of_finite k R`.

Use `haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _`. Set `N` to `nilradical R`. Set `f : R →ₐ[k] R ⧸ N` to `Ideal.Quotient.mkₐ k N`. Establish `hf : ∀ r, f r = Ideal.Quotient.mk N r` using `fun r => rfl`. Establish `hfN : ∀ r, f r = 0 ↔ IsNilpotent r` using `fun r => by`.

Rewrite using `[hf, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `mem_nilradical`. Use `haveI : IsReduced (R ⧸ N) := (Ideal.isRadical_iff_quotient_reduced N).mp (Ideal.radical_isRadical _)`. Use `haveI : FiniteDimensional k (R ⧸ N) := Module.Finite.of_surjective f.toLinearMap Ideal.Quotient.mk_surjective`. Establish `hrootbar : ∀ a : k, ∃ w : R ⧸ N, w ^ (p ^ c) = algebraMap k (R ⧸ N) a` using `fun a => by`.

Take `⟨w, hw⟩` from `hroot a`. Conclude with `⟨f w, by rw [← map_pow, hw, AlgHom.commutes]⟩`. Take `⟨n, hn, -⟩` from `fieldGen (k := k) (E := Tw k p c) p c (fun a => ⟨(a : k), rfl⟩)`. Establish `hα : ∀ I : MaximalSpectrum R, ∃ α : Fin n → R ⧸ I.asIdeal, Algebra.adjoin k (Set.range (fun b : R ⧸ I.asIdeal => b ^ (p ^ c)) ∪ Set.range α) = ⊤`. Introduce `I`.

Use `haveI := I.isMaximal`. Use `letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal`. Use `haveI : FiniteDimensional k (R ⧸ I.asIdeal) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap Ideal.Quotient.mk_surjective`. Take `⟨n', hn', α, hα⟩` from `fieldGen (k := k) (E := R ⧸ I.asIdeal) p c (fun a => by`. Take `⟨w, hw⟩` from `hroot a`.

Conclude with `⟨Ideal.Quotient.mkₐ k I.asIdeal w, by rw [← map_pow, hw, AlgHom.commutes]⟩)`. Establish `: n' = n` using `Nat.pow_right_injective hq2 (hn'.symm.trans hn)`. Substitute `this` using the available equality. Conclude with `⟨α, hα⟩`. Use `choose α hα using hα`.

Set `π : (R ⧸ N) ≃ₐ[k] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal` to `(IsArtinianRing.quotNilradicalEquivPi R).restrictScalars k`. Set `Lbar : Fin n → R ⧸ N` to `fun i => π.symm (fun I => α I i)`. Set `σ : ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal → R ⧸ N` to `fun I z => π.symm (Pi.single I z)`. Establish `hσadd : ∀ I z w, σ I (z + w) = σ I z + σ I w` using `fun I z w => by`. Simplify using `only [σ, Pi.single_add, map_add]`.

Establish `hσmul : ∀ I z w, σ I (z * w) = σ I z * σ I w` using `fun I z w => by`. Simplify using `only [σ, Pi.single_mul, map_mul]`. Establish `hσpow : ∀ I z, σ I (z ^ (p ^ c)) = σ I z ^ (p ^ c)` using `fun I z => by`. Apply `π.injective` to reduce the goal to its premises. Simplify using `only [σ, map_pow, AlgEquiv.apply_symm_apply]`.

Use function extensionality and compare the values at `J`. Distinguish the cases in `h : J = I`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h, zero_pow hq0.ne']`.

Establish `hσalg : ∀ I (a : k), σ I (algebraMap k _ a) = algebraMap k (R ⧸ N) a * σ I 1` using `fun I a => by`. Apply `π.injective` to reduce the goal to its premises. Simplify using `only [σ, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]`. Use function extensionality and compare the values at `J`. Distinguish the cases in `h : J = I`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Establish `hσL : ∀ I i, σ I (α I i) = σ I 1 * Lbar i` using `fun I i => by`. Apply `π.injective` to reduce the goal to its premises.

Simplify using `only [σ, Lbar, map_mul, AlgEquiv.apply_symm_apply]`. Use function extensionality and compare the values at `J`. Distinguish the cases in `h : J = I`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[h]`. Set `A` to `Algebra.adjoin k (Set.range (fun b : R ⧸ N => b ^ (p ^ c)) ∪ Set.range Lbar)`. Establish `he : ∀ I, σ I 1 ∈ A` using `fun I => by`. Establish `: σ I 1 = σ I 1 ^ (p ^ c)` using `by rw [← hσpow, one_pow]`. Rewrite using `[this]`.

Conclude with `Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)`. Establish `hσA : ∀ I z, σ I z ∈ A`. Introduce `I z`. Establish `hz : z ∈ Algebra.adjoin k (Set.range (fun b : R ⧸ I.asIdeal => b ^ (p ^ c)) ∪ Set.range (α I))`. Rewrite using `[hα I]`.

Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hz using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with ⟨b, rfl⟩ | ⟨i, rfl⟩` into its components or cases. Rewrite using `[hσpow]`.

Conclude with `Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)`. Rewrite using `[hσL]`. Conclude with `A.mul_mem (he I) (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))`. Consider the case `algebraMap a => rw [hσalg]`. Conclude with `A.mul_mem (A.algebraMap_mem a) (he I)`.

Consider the case `add x y _ _ hx hy => rw [hσadd]`. Conclude with `A.add_mem hx hy`. Consider the case `mul x y _ _ hx hy => rw [hσmul]`. Conclude with `A.mul_mem hx hy`. Establish `hAtop : ∀ x : R ⧸ N, x ∈ A`.

Introduce `x`. Establish `: x = ∑ I, σ I (π x I)`. Apply `π.injective` to reduce the goal to its premises. Rewrite using `[map_sum]`. Simplify using `only [σ, AlgEquiv.apply_symm_apply]`.

Conclude with `(Finset.univ_sum_single (π x)).symm`. Rewrite using `[this]`. Conclude with `A.sum_mem fun I _ => hσA I _`. Use `choose L hL using fun i => Ideal.Quotient.mk_surjective (I := N) (Lbar i)`. Set `T` to `Pw k R (p ^ c)`.

Establish `hLq : ∀ i, L i ^ (p ^ c) ∈ T` using `fun i => Algebra.subset_adjoin ⟨L i, rfl⟩`. Set `S` to `Algebra.adjoin k ((T : Set R) ∪ Set.range L)`. Establish `hAS : A ≤ S.map f` using `Algebra.adjoin_le (by`. Introduce and unpack `_ (⟨b, rfl⟩ | ⟨i, rfl⟩)`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Conclude with `⟨r ^ (p ^ c), Algebra.subset_adjoin (Or.inl (Algebra.subset_adjoin ⟨r, rfl⟩)), by rw [map_pow]; rfl⟩`. Conclude with `⟨L i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩), hL i⟩)`. Establish `hlift : ∀ r : R, ∃ s ∈ S, f s = f r` using `fun r => hAS (hAtop (f r))`. Set `g : S →ₗ[k] R ⧸ N` to `f.toLinearMap ∘ₗ S.val.toLinearMap`. Establish `hg : Function.Surjective g`.

Introduce `x`. Take `⟨r, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Take `⟨s, hs, hfs⟩` from `hlift r`. Conclude with `⟨⟨s, hs⟩, hfs⟩`. Establish `hS : finrank k S ≤ (p ^ c) ^ n * finrank k T` using `finrank_adjoin_pow_le T (p ^ c) n hq0 L hLq`.

Establish `hTmem : ∀ t : T, f t ∈ Subalgebra.toSubmodule (Pw k (R ⧸ N) (p ^ c))`. Introduce `t`. Take `⟨w, hw⟩` from `(mem_Pw p c hroot).mp t.2`. Use `show f t ∈ Pw k (R ⧸ N) (p ^ c)`. Rewrite using `[← hw, map_pow]`.

Conclude with `Algebra.subset_adjoin ⟨f w, rfl⟩`. Set `h : T →ₗ[k] Subalgebra.toSubmodule (Pw k (R ⧸ N) (p ^ c))` to `LinearMap.codRestrict _ (f.toLinearMap ∘ₗ T.val.toLinearMap) hTmem`. Establish `hinj : Function.Injective h`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `t ht`.

Establish `h0 : f t = 0` using `congrArg Subtype.val ht`. Take `⟨w, hw⟩` from `(mem_Pw p c hroot).mp t.2`. Take `⟨m, hm⟩` from `(hfN _).mp h0`. Establish `hwn : IsNilpotent w` using `⟨p ^ c * m, by rw [pow_mul, hw, hm]⟩`. Conclude with `Subtype.ext (by rw [← hw, hnil w hwn]; rfl)`.

Establish `hT : finrank k T ≤ finrank k (Pw k (R ⧸ N) (p ^ c))`. Rewrite using `[← Subalgebra.finrank_toSubmodule (Pw k (R ⧸ N) (p ^ c))]`. Conclude with `LinearMap.finrank_le_finrank_of_injective hinj`. Establish `hfc` using `fc (B := R ⧸ N) p c hrootbar`. Rewrite `hfc` using `[hn]`.

Establish `hbar : finrank k (R ⧸ N) ≤ finrank k S`. Rewrite using `[← finrank_top k (R ⧸ N), ← LinearMap.range_eq_top.mpr hg]`. Conclude with `LinearMap.finrank_range_le g`. Establish `heq : finrank k S = finrank k (R ⧸ N)`. Use `le_antisymm ?_ hbar` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Establish `hginj : Function.Injective g` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hg`. Use `⟨S, fun s hs hsn => ?_, fun r => ?_⟩` and prove the remaining obligations. Establish `: g ⟨s, hs⟩ = g 0`. Rewrite using `[map_zero]`.

Conclude with `(hfN s).mpr hsn`. Conclude with `congrArg Subtype.val (hginj this)`. Take `⟨s, hs, hfs⟩` from `hlift r`. Use `⟨s, hs, (hfN _).mp ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, hfs, sub_self]`.
-/
theorem sectionEx {k R : Type*} [Field k] [CommRing R] [Algebra k R] [FiniteDimensional k R]
    (p c : ℕ) [Fact p.Prime] [CharP k p] [FiniteDimensional k (Tw k p c)]
    (hnil : ∀ r : R, IsNilpotent r → r ^ (p ^ c) = 0)
    (hroot : ∀ a : k, ∃ w : R, w ^ (p ^ c) = algebraMap k R a) :
    ∃ S : Subalgebra k R, (∀ s ∈ S, IsNilpotent s → s = 0) ∧ ∀ r : R, ∃ s ∈ S, IsNilpotent (r - s) := by
  classical
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · refine ⟨⊤, fun s _ hs => by simpa using hnil s hs, fun r => ⟨r, Algebra.mem_top, by simp⟩⟩
  have hq2 : 2 ≤ p ^ c := le_trans (Fact.out : p.Prime).two_le (Nat.le_self_pow hc.ne' p)
  have hq0 : 0 < p ^ c := by omega
  haveI : IsArtinianRing R := IsArtinianRing.of_finite k R
  haveI : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  let N := nilradical R
  let f : R →ₐ[k] R ⧸ N := Ideal.Quotient.mkₐ k N
  have hf : ∀ r, f r = Ideal.Quotient.mk N r := fun r => rfl
  have hfN : ∀ r, f r = 0 ↔ IsNilpotent r := fun r => by
    rw [hf, Ideal.Quotient.eq_zero_iff_mem]; exact mem_nilradical
  haveI : IsReduced (R ⧸ N) :=
    (Ideal.isRadical_iff_quotient_reduced N).mp (Ideal.radical_isRadical _)
  haveI : FiniteDimensional k (R ⧸ N) :=
    Module.Finite.of_surjective f.toLinearMap Ideal.Quotient.mk_surjective
  have hrootbar : ∀ a : k, ∃ w : R ⧸ N, w ^ (p ^ c) = algebraMap k (R ⧸ N) a := fun a => by
    obtain ⟨w, hw⟩ := hroot a
    exact ⟨f w, by rw [← map_pow, hw, AlgHom.commutes]⟩

  obtain ⟨n, hn, -⟩ := fieldGen (k := k) (E := Tw k p c) p c
    (fun a => ⟨(a : k), rfl⟩)

  have hα : ∀ I : MaximalSpectrum R, ∃ α : Fin n → R ⧸ I.asIdeal,
      Algebra.adjoin k (Set.range (fun b : R ⧸ I.asIdeal => b ^ (p ^ c)) ∪ Set.range α) = ⊤ := by
    intro I
    haveI := I.isMaximal
    letI : Field (R ⧸ I.asIdeal) := Ideal.Quotient.field I.asIdeal
    haveI : FiniteDimensional k (R ⧸ I.asIdeal) :=
      Module.Finite.of_surjective (Ideal.Quotient.mkₐ k I.asIdeal).toLinearMap
        Ideal.Quotient.mk_surjective
    obtain ⟨n', hn', α, hα⟩ := fieldGen (k := k) (E := R ⧸ I.asIdeal) p c (fun a => by
      obtain ⟨w, hw⟩ := hroot a
      exact ⟨Ideal.Quotient.mkₐ k I.asIdeal w, by rw [← map_pow, hw, AlgHom.commutes]⟩)
    have : n' = n := Nat.pow_right_injective hq2 (hn'.symm.trans hn)
    subst this
    exact ⟨α, hα⟩
  choose α hα using hα
  let π : (R ⧸ N) ≃ₐ[k] ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal :=
    (IsArtinianRing.quotNilradicalEquivPi R).restrictScalars k
  let Lbar : Fin n → R ⧸ N := fun i => π.symm (fun I => α I i)
  let σ : ∀ I : MaximalSpectrum R, R ⧸ I.asIdeal → R ⧸ N := fun I z => π.symm (Pi.single I z)
  have hσadd : ∀ I z w, σ I (z + w) = σ I z + σ I w := fun I z w => by
    simp only [σ, Pi.single_add, map_add]
  have hσmul : ∀ I z w, σ I (z * w) = σ I z * σ I w := fun I z w => by
    simp only [σ, Pi.single_mul, map_mul]
  have hσpow : ∀ I z, σ I (z ^ (p ^ c)) = σ I z ^ (p ^ c) := fun I z => by
    apply π.injective
    simp only [σ, map_pow, AlgEquiv.apply_symm_apply]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h, zero_pow hq0.ne']
  have hσalg : ∀ I (a : k), σ I (algebraMap k _ a) = algebraMap k (R ⧸ N) a * σ I 1 := fun I a => by
    apply π.injective
    simp only [σ, map_mul, AlgEquiv.apply_symm_apply, AlgEquiv.commutes]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h]
  have hσL : ∀ I i, σ I (α I i) = σ I 1 * Lbar i := fun I i => by
    apply π.injective
    simp only [σ, Lbar, map_mul, AlgEquiv.apply_symm_apply]
    funext J
    by_cases h : J = I
    · subst h; simp
    · simp [h]
  let A := Algebra.adjoin k (Set.range (fun b : R ⧸ N => b ^ (p ^ c)) ∪ Set.range Lbar)
  have he : ∀ I, σ I 1 ∈ A := fun I => by
    have : σ I 1 = σ I 1 ^ (p ^ c) := by rw [← hσpow, one_pow]
    rw [this]; exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
  have hσA : ∀ I z, σ I z ∈ A := by
    intro I z
    have hz : z ∈ Algebra.adjoin k
        (Set.range (fun b : R ⧸ I.asIdeal => b ^ (p ^ c)) ∪ Set.range (α I)) := by
      rw [hα I]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨b, rfl⟩ | ⟨i, rfl⟩
      · rw [hσpow]; exact Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩)
      · rw [hσL]; exact A.mul_mem (he I) (Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩))
    | algebraMap a => rw [hσalg]; exact A.mul_mem (A.algebraMap_mem a) (he I)
    | add x y _ _ hx hy => rw [hσadd]; exact A.add_mem hx hy
    | mul x y _ _ hx hy => rw [hσmul]; exact A.mul_mem hx hy
  have hAtop : ∀ x : R ⧸ N, x ∈ A := by
    intro x
    have : x = ∑ I, σ I (π x I) := by
      apply π.injective
      rw [map_sum]
      simp only [σ, AlgEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single (π x)).symm
    rw [this]; exact A.sum_mem fun I _ => hσA I _

  choose L hL using fun i => Ideal.Quotient.mk_surjective (I := N) (Lbar i)
  let T := Pw k R (p ^ c)
  have hLq : ∀ i, L i ^ (p ^ c) ∈ T := fun i => Algebra.subset_adjoin ⟨L i, rfl⟩
  let S := Algebra.adjoin k ((T : Set R) ∪ Set.range L)
  have hAS : A ≤ S.map f := Algebra.adjoin_le (by
    rintro _ (⟨b, rfl⟩ | ⟨i, rfl⟩)
    · obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
      exact ⟨r ^ (p ^ c), Algebra.subset_adjoin (Or.inl (Algebra.subset_adjoin ⟨r, rfl⟩)),
        by rw [map_pow]; rfl⟩
    · exact ⟨L i, Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩), hL i⟩)
  have hlift : ∀ r : R, ∃ s ∈ S, f s = f r := fun r => hAS (hAtop (f r))

  let g : S →ₗ[k] R ⧸ N := f.toLinearMap ∘ₗ S.val.toLinearMap
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨s, hs, hfs⟩ := hlift r
    exact ⟨⟨s, hs⟩, hfs⟩
  have hS : finrank k S ≤ (p ^ c) ^ n * finrank k T :=
    finrank_adjoin_pow_le T (p ^ c) n hq0 L hLq
  have hTmem : ∀ t : T, f t ∈ Subalgebra.toSubmodule (Pw k (R ⧸ N) (p ^ c)) := by
    intro t
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).mp t.2
    show f t ∈ Pw k (R ⧸ N) (p ^ c)
    rw [← hw, map_pow]
    exact Algebra.subset_adjoin ⟨f w, rfl⟩
  let h : T →ₗ[k] Subalgebra.toSubmodule (Pw k (R ⧸ N) (p ^ c)) :=
    LinearMap.codRestrict _ (f.toLinearMap ∘ₗ T.val.toLinearMap) hTmem
  have hinj : Function.Injective h := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    have h0 : f t = 0 := congrArg Subtype.val ht
    obtain ⟨w, hw⟩ := (mem_Pw p c hroot).mp t.2
    obtain ⟨m, hm⟩ := (hfN _).mp h0
    have hwn : IsNilpotent w := ⟨p ^ c * m, by rw [pow_mul, hw, hm]⟩
    exact Subtype.ext (by rw [← hw, hnil w hwn]; rfl)
  have hT : finrank k T ≤ finrank k (Pw k (R ⧸ N) (p ^ c)) := by
    rw [← Subalgebra.finrank_toSubmodule (Pw k (R ⧸ N) (p ^ c))]
    exact LinearMap.finrank_le_finrank_of_injective hinj
  have hfc := fc (B := R ⧸ N) p c hrootbar
  rw [hn] at hfc
  have hbar : finrank k (R ⧸ N) ≤ finrank k S := by
    rw [← finrank_top k (R ⧸ N), ← LinearMap.range_eq_top.mpr hg]
    exact LinearMap.finrank_range_le g
  have heq : finrank k S = finrank k (R ⧸ N) := by
    refine le_antisymm ?_ hbar
    calc finrank k S ≤ (p ^ c) ^ n * finrank k T := hS
      _ ≤ (p ^ c) ^ n * finrank k (Pw k (R ⧸ N) (p ^ c)) := Nat.mul_le_mul_left _ hT
      _ = finrank k (R ⧸ N) := hfc.symm
  have hginj : Function.Injective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr hg
  refine ⟨S, fun s hs hsn => ?_, fun r => ?_⟩
  · have : g ⟨s, hs⟩ = g 0 := by
      rw [map_zero]; exact (hfN s).mpr hsn
    exact congrArg Subtype.val (hginj this)
  · obtain ⟨s, hs, hfs⟩ := hlift r
    refine ⟨s, hs, (hfN _).mp ?_⟩
    rw [map_sub, hfs, sub_self]

end PositivityTheory.RgUd.TP.Desc.Piece.PSect

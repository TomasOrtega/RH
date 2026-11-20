import Mathlib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open IsLocalRing Ideal

universe u

variable {R : Type u} [CommRing R]

/- English proof (translation)
Use `set m := maximalIdeal R with hm`. Set `x' : m` to `⟨x, hx⟩`. Set `v0 : CotangentSpace R` to `m.toCotangent x'`. Establish `hx0 : v0 ≠ 0`. Rewrite using `[Ne, Ideal.toCotangent_eq_zero]`.

Simplify `hx2` using `[pow_two]`. Set `L : Submodule (ResidueField R) (CotangentSpace R)` to `Submodule.span _ {v0}`. Establish `hL : Module.finrank (ResidueField R) L = 1` using `finrank_span_singleton hx0`. Use `set q := Module.finrank (ResidueField R) (CotangentSpace R ⧸ L) with hq`. Establish `hdim : q + 1 = Module.finrank (ResidueField R) (CotangentSpace R)`.

Rewrite using `[hq, ← hL, L.finrank_quotient_add_finrank]`. Set `bW` to `Module.finBasis (ResidueField R) (CotangentSpace R ⧸ L)`. Establish `hlift : ∀ i : Fin q, ∃ y : m, L.mkQ (m.toCotangent y) = bW i`. Introduce `i`. Take `⟨v, hv⟩` from `L.mkQ_surjective (bW i)`.

Take `⟨y, rfl⟩` from `m.toCotangent_surjective v`. Conclude with `⟨y, hv⟩`. Use `choose t ht using hlift`. Set `s : Set m` to `insert x' (Set.range t)`. Establish `hspan : Submodule.span (ResidueField R) (m.toCotangent '' s) = ⊤` using `by set S := Submodule.span (ResidueField R) (m.toCotangent '' s)`.

Establish `hLS : L ≤ S` using `Submodule.span_le.mpr (by`. Introduce and unpack `_ rfl`. Conclude with `Submodule.subset_span ⟨x', Set.mem_insert _ _, rfl⟩)`. Establish `hmap : S.map L.mkQ = ⊤`. Rewrite using `[eq_top_iff, ← bW.span_eq, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨m.toCotangent (t i), Submodule.subset_span ⟨t i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩, ht i⟩`. Rewrite `hmap` using `[Submodule.map_mkQ_eq_top]`. Rewrite `hmap` using `[sup_eq_right.mpr hLS]`. Then use the resulting hypothesis. Establish `hspanR : Submodule.span R s = ⊤` using `CotangentSpace.span_image_eq_top_iff.mp hspan`.

Establish `hmspan : m = Ideal.span (Subtype.val '' s)`. Use `Submodule.map_span m.subtype s` as an intermediate fact. Rewrite `this` using `[hspanR, Submodule.map_subtype_top]`. Conclude with `this`. Establish `hmax : maximalIdeal (R ⧸ span {x}) = Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R)))`.

Rewrite using `[← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hm, congrArg (Ideal.map (Ideal.Quotient.mk (span {x}))) hmspan, Ideal.map_span]`. Establish `: (Ideal.Quotient.mk (span {x})) '' (Subtype.val '' s) = insert 0 (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R)))`. Simplify using `only [s, Set.image_insert_eq, ← Set.range_comp]`. Use `congr 1`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)`.

Rewrite using `[this, Ideal.span_insert_zero]`. Establish `hle : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ q`. Rewrite using `[hmax]`. Establish `hfin : (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) = ((Finset.univ.image (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R)) : Finset (R ⧸ span {x})) : Set (R ⧸ span {x}))` using `by simp`. Use `(Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_` and prove the remaining obligations.

Rewrite using `[hfin, Set.ncard_coe_finset]`. Conclude with `(Finset.card_image_le).trans (by simp)`. Establish `hmr : m.spanFinrank = q + 1`. Rewrite using `[hm, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)]`. Conclude with `hdim.symm`.

Use linear arithmetic over natural numbers and integers.
-/
theorem spanFinrank_maximalIdeal_quotient_add_one_le [IsLocalRing R] [IsNoetherianRing R]
    {x : R} (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    [IsLocalRing (R ⧸ span {x})] :
    (maximalIdeal (R ⧸ span {x})).spanFinrank + 1 ≤ (maximalIdeal R).spanFinrank := by
  classical
  set m := maximalIdeal R with hm
  let x' : m := ⟨x, hx⟩
  let v0 : CotangentSpace R := m.toCotangent x'
  have hx0 : v0 ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]
    simpa [pow_two] using hx2
  let L : Submodule (ResidueField R) (CotangentSpace R) := Submodule.span _ {v0}
  have hL : Module.finrank (ResidueField R) L = 1 := finrank_span_singleton hx0
  set q := Module.finrank (ResidueField R) (CotangentSpace R ⧸ L) with hq
  have hdim : q + 1 = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [hq, ← hL, L.finrank_quotient_add_finrank]
  let bW := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ L)
  have hlift : ∀ i : Fin q, ∃ y : m, L.mkQ (m.toCotangent y) = bW i := by
    intro i
    obtain ⟨v, hv⟩ := L.mkQ_surjective (bW i)
    obtain ⟨y, rfl⟩ := m.toCotangent_surjective v
    exact ⟨y, hv⟩
  choose t ht using hlift
  let s : Set m := insert x' (Set.range t)
  have hspan : Submodule.span (ResidueField R) (m.toCotangent '' s) = ⊤ := by
    set S := Submodule.span (ResidueField R) (m.toCotangent '' s)
    have hLS : L ≤ S := Submodule.span_le.mpr (by
      rintro _ rfl
      exact Submodule.subset_span ⟨x', Set.mem_insert _ _, rfl⟩)
    have hmap : S.map L.mkQ = ⊤ := by
      rw [eq_top_iff, ← bW.span_eq, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨m.toCotangent (t i), Submodule.subset_span ⟨t i, Set.mem_insert_of_mem _ ⟨i, rfl⟩, rfl⟩,
        ht i⟩
    rw [Submodule.map_mkQ_eq_top] at hmap
    rwa [sup_eq_right.mpr hLS] at hmap
  have hspanR : Submodule.span R s = ⊤ := CotangentSpace.span_image_eq_top_iff.mp hspan
  have hmspan : m = Ideal.span (Subtype.val '' s) := by
    have := Submodule.map_span m.subtype s
    rw [hspanR, Submodule.map_subtype_top] at this
    exact this
  have hmax : maximalIdeal (R ⧸ span {x}) =
      Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
    rw [← map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective, ← hm,
      congrArg (Ideal.map (Ideal.Quotient.mk (span {x}))) hmspan, Ideal.map_span]
    have : (Ideal.Quotient.mk (span {x})) '' (Subtype.val '' s) =
        insert 0 (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) := by
      simp only [s, Set.image_insert_eq, ← Set.range_comp]
      congr 1
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
    rw [this, Ideal.span_insert_zero]
  have hle : (maximalIdeal (R ⧸ span {x})).spanFinrank ≤ q := by
    rw [hmax]
    have hfin : (Set.range (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R))) =
        ((Finset.univ.image (fun i ↦ Ideal.Quotient.mk (span {x}) (t i : R)) :
          Finset (R ⧸ span {x})) : Set (R ⧸ span {x})) := by simp
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range _)).trans ?_
    rw [hfin, Set.ncard_coe_finset]
    exact (Finset.card_image_le).trans (by simp)
  have hmr : m.spanFinrank = q + 1 := by
    rw [hm, spanFinrank_maximalIdeal_eq_finrank_cotangentSpace (R := R)]
    exact hdim.symm
  omega

/- English proof (translation)
Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot => simp at h2`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top`.

It suffices to derive a contradiction. Establish `h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((b : ℕ∞) : WithBot ℕ∞)` using `h3`. Rewrite `h4` using `[WithBot.coe_le_coe, top_le_iff]`. Conclude with `ENat.natCast_ne_top b h4`. Consider the case `coe k => exact ⟨k, rfl⟩`.
-/
private lemma exists_nat_of_le_add_one {d : WithBot ℕ∞} {n b : ℕ} (h2 : (n : WithBot ℕ∞) ≤ d + 1)
    (h3 : d ≤ b) : ∃ k : ℕ, d = k := by
  induction d using WithBot.recBotCoe with
  | bot => simp at h2
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h4 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((b : ℕ∞) : WithBot ℕ∞) := h3
      rw [WithBot.coe_le_coe, top_le_iff] at h4
      exact ENat.natCast_ne_top b h4
    | coe k => exact ⟨k, rfl⟩

/- English proof (translation)
Establish `h1` using `spanFinrank_maximalIdeal_quotient_add_one_le hx hx2`. Establish `hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞)` using `((isRegularLocalRing_iff R).mp inferInstance).symm`. Establish `h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1`. Use `(ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (span {x}) ?_).trans ?_` and prove the remaining obligations. Rewrite using `[IsLocalRing.ringJacobson_eq_maximalIdeal]`.

Conclude with `(span_singleton_le_iff_mem _).mpr hx`. Use `gcongr`. Conclude with `(Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans (by simp)` after adjusting the coercions. Establish `h3` using `ringKrullDim_le_spanFinrank_maximalIdeal (R := R ⧸ span {x})`. Rewrite `h2` using `[hR]`.

Take `⟨k, hk⟩` from `exists_nat_of_le_add_one h2 h3`. Rewrite `h2`, `h3`, the goal using `[hk]`. Establish `h2' : (maximalIdeal R).spanFinrank ≤ k + 1` using `by exact_mod_cast h2`. Establish `h3' : k ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank` using `by exact_mod_cast h3`. Establish `hk' : (maximalIdeal (R ⧸ span {x})).spanFinrank = k` using `by omega`.

Use `⟨(isRegularLocalRing_iff _).mpr (by rw [hk, hk']), ?_⟩` and prove the remaining obligations. Rewrite using `[hR]`. Conclude with `(by omega : k + 1 = (maximalIdeal R).spanFinrank)` after adjusting the coercions.
-/
theorem isRegularLocalRing_quotient [IsRegularLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) [IsLocalRing (R ⧸ span {x})] :
    IsRegularLocalRing (R ⧸ span {x}) ∧ ringKrullDim (R ⧸ span {x}) + 1 = ringKrullDim R := by
  have h1 := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
  have hR : ringKrullDim R = ((maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    ((isRegularLocalRing_iff R).mp inferInstance).symm
  have h2 : ringKrullDim R ≤ ringKrullDim (R ⧸ span {x}) + 1 := by
    refine (ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank (span {x}) ?_).trans ?_
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact (span_singleton_le_iff_mem _).mpr hx
    · gcongr
      exact_mod_cast (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_singleton x)).trans
        (by simp)
  have h3 := ringKrullDim_le_spanFinrank_maximalIdeal (R := R ⧸ span {x})
  rw [hR] at h2
  obtain ⟨k, hk⟩ := exists_nat_of_le_add_one h2 h3
  rw [hk] at h2 h3 ⊢
  have h2' : (maximalIdeal R).spanFinrank ≤ k + 1 := by exact_mod_cast h2
  have h3' : k ≤ (maximalIdeal (R ⧸ span {x})).spanFinrank := by exact_mod_cast h3
  have hk' : (maximalIdeal (R ⧸ span {x})).spanFinrank = k := by omega
  refine ⟨(isRegularLocalRing_iff _).mpr (by rw [hk, hk']), ?_⟩
  rw [hR]
  exact_mod_cast (by omega : k + 1 = (maximalIdeal R).spanFinrank)

/- English proof (translation)
It suffices to establish `H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S], (maximalIdeal S).spanFinrank = n → IsDomain S from H _ R rfl`. Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `S _ _ hn`.

Establish `hfg : (maximalIdeal S).FG` using `(maximalIdeal S).fg_of_isNoetherianRing`. Distinguish the cases in `h0 : n = 0`. Establish `hbot : maximalIdeal S = ⊥` using `(Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp (hn.trans h0)`. Set `` to `((isField_iff_maximalIdeal_eq).mpr hbot).toField`. Use `infer_instance`.

Establish `hdim : ringKrullDim S = (n : WithBot ℕ∞)`. Rewrite using `[← hn]`. Conclude with `((isRegularLocalRing_iff S).mp inferInstance).symm`. Establish `hjac : maximalIdeal S ≤ jacobson ⊥` using `(IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge`. Establish `hmin : ∀ P ∈ minimalPrimes S, ¬ maximalIdeal S ≤ P`.

Introduce `P hP hle`. Establish `hPm : P = maximalIdeal S` using `le_antisymm (IsLocalRing.le_maximalIdeal hP.1.1.ne_top) hle`. Establish `: (maximalIdeal S).height = 0`. Rewrite using `[Ideal.height_eq_zero_iff, ← hPm]`. Conclude with `hP`.

Rewrite `hdim` using `[← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, this]`. Conclude with `h0 (by exact_mod_cast hdim.symm)`. Establish `hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2`. Introduce `hle`. Establish `: maximalIdeal S = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg (by simpa [pow_two, smul_eq_mul] using hle) hjac`.

Conclude with `h0 (by rw [← hn, this]; simp)`. Establish `hfin` using `minimalPrimes.finite_of_isNoetherianRing S`. Take `⟨x, hx, hxn⟩ : ∃ x ∈ maximalIdeal S, x ∉ ⋃ i ∈ (↑(insert (maximalIdeal S ^ 2) hfin.toFinset) : Set (Ideal S)), (i : Set S)` from `by by_contra! hcon`. Take `⟨i, hi, hle⟩` from `(Ideal.subset_union_prime (f := id) (maximalIdeal S ^ 2) (maximalIdeal S ^ 2) (fun i hi h1 _ ↦ by`. Break down `Finset.mem_insert.mp hi with h | h` into its components or cases.

Conclude with `absurd h h1`. Conclude with `((Set.Finite.mem_toFinset _).mp h).1.1)).mp hcon`. Break down `Finset.mem_insert.mp hi with h | h` into its components or cases. Conclude with `hsq (h ▸ hle)`. Conclude with `hmin i ((Set.Finite.mem_toFinset _).mp h) hle`.

Simplify using `only [Finset.coe_insert, Set.Finite.coe_toFinset, Set.mem_insert_iff, Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxn`. Take `⟨hx2, hxP⟩` from `hxn`. Establish `hne : span {x} ≠ ⊤` using `fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))`. Establish `: Nontrivial (S ⧸ span {x})` using `Ideal.Quotient.nontrivial_iff.mpr hne`. Establish `: IsLocalRing (S ⧸ span {x})` using `.of_surjective' _ Ideal.Quotient.mk_surjective`.

Take `⟨hreg, -⟩` from `isRegularLocalRing_quotient hx hx2`. Establish `hlt` using `spanFinrank_maximalIdeal_quotient_add_one_le hx hx2`. Use `ih _ (by omega) (S ⧸ span {x}) rfl` as an intermediate fact. Establish `hprime : (span {x} : Ideal S).IsPrime` using `(Ideal.Quotient.isDomain_iff_prime _).mp inferInstance`. Take `⟨P, hP, hPle⟩` from `Ideal.exists_minimalPrimes_le (I := ⊥) (J := span {x}) bot_le`.

Establish `hxP' : x ∉ P` using `hxP P hP`. Establish `hPsmul : P ≤ maximalIdeal S • P`. Introduce `y hy`. Take `⟨z, rfl⟩` from `Ideal.mem_span_singleton'.mp (hPle hy)`. Establish `hz : z ∈ P` using `(hP.1.1.mem_or_mem hy).resolve_right hxP'`.

Rewrite using `[mul_comm]`. Conclude with `Submodule.smul_mem_smul hx hz`. Establish `hPbot : P = ⊥` using `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ P.fg_of_isNoetherianRing hPsmul hjac`. Establish `: (⊥ : Ideal S).IsPrime` using `hPbot ▸ hP.1.1`. Conclude with `IsDomain.of_bot_isPrime S`.
-/
theorem IsRegularLocalRing.isDomain [IsRegularLocalRing R] : IsDomain R := by
  suffices H : ∀ n : ℕ, ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      (maximalIdeal S).spanFinrank = n → IsDomain S from H _ R rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S _ _ hn
  have hfg : (maximalIdeal S).FG := (maximalIdeal S).fg_of_isNoetherianRing
  by_cases h0 : n = 0
  · have hbot : maximalIdeal S = ⊥ :=
      (Submodule.spanFinrank_eq_zero_iff_eq_bot hfg).mp (hn.trans h0)
    let := ((isField_iff_maximalIdeal_eq).mpr hbot).toField
    infer_instance
  · have hdim : ringKrullDim S = (n : WithBot ℕ∞) := by
      rw [← hn]; exact ((isRegularLocalRing_iff S).mp inferInstance).symm
    have hjac : maximalIdeal S ≤ jacobson ⊥ :=
      (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    have hmin : ∀ P ∈ minimalPrimes S, ¬ maximalIdeal S ≤ P := by
      intro P hP hle
      have hPm : P = maximalIdeal S :=
        le_antisymm (IsLocalRing.le_maximalIdeal hP.1.1.ne_top) hle
      have : (maximalIdeal S).height = 0 := by
        rw [Ideal.height_eq_zero_iff, ← hPm]; exact hP
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, this] at hdim
      exact h0 (by exact_mod_cast hdim.symm)
    have hsq : ¬ maximalIdeal S ≤ maximalIdeal S ^ 2 := by
      intro hle
      have : maximalIdeal S = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ hfg
        (by simpa [pow_two, smul_eq_mul] using hle) hjac
      exact h0 (by rw [← hn, this]; simp)
    classical
    have hfin := minimalPrimes.finite_of_isNoetherianRing S
    obtain ⟨x, hx, hxn⟩ : ∃ x ∈ maximalIdeal S,
        x ∉ ⋃ i ∈ (↑(insert (maximalIdeal S ^ 2) hfin.toFinset) : Set (Ideal S)), (i : Set S) := by
      by_contra! hcon
      obtain ⟨i, hi, hle⟩ := (Ideal.subset_union_prime (f := id) (maximalIdeal S ^ 2)
        (maximalIdeal S ^ 2) (fun i hi h1 _ ↦ by
          rcases Finset.mem_insert.mp hi with h | h
          · exact absurd h h1
          · exact ((Set.Finite.mem_toFinset _).mp h).1.1)).mp hcon
      rcases Finset.mem_insert.mp hi with h | h
      · exact hsq (h ▸ hle)
      · exact hmin i ((Set.Finite.mem_toFinset _).mp h) hle
    simp only [Finset.coe_insert, Set.Finite.coe_toFinset, Set.mem_insert_iff,
      Set.iUnion_iUnion_eq_or_left, Set.mem_union, Set.mem_iUnion, not_or, not_exists] at hxn
    obtain ⟨hx2, hxP⟩ := hxn
    have hne : span {x} ≠ ⊤ := fun h ↦ (IsLocalRing.maximalIdeal.isMaximal S).ne_top
      (top_le_iff.mp (h ▸ (span_singleton_le_iff_mem _).mpr hx))
    have : Nontrivial (S ⧸ span {x}) := Ideal.Quotient.nontrivial_iff.mpr hne
    have : IsLocalRing (S ⧸ span {x}) := .of_surjective' _ Ideal.Quotient.mk_surjective
    obtain ⟨hreg, -⟩ := isRegularLocalRing_quotient hx hx2
    have hlt := spanFinrank_maximalIdeal_quotient_add_one_le hx hx2
    have := ih _ (by omega) (S ⧸ span {x}) rfl
    have hprime : (span {x} : Ideal S).IsPrime :=
      (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
    obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := span {x}) bot_le
    have hxP' : x ∉ P := hxP P hP
    have hPsmul : P ≤ maximalIdeal S • P := by
      intro y hy
      obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton'.mp (hPle hy)
      have hz : z ∈ P := (hP.1.1.mem_or_mem hy).resolve_right hxP'
      rw [mul_comm]
      exact Submodule.smul_mem_smul hx hz
    have hPbot : P = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
      P.fg_of_isNoetherianRing hPsmul hjac
    have : (⊥ : Ideal S).IsPrime := hPbot ▸ hP.1.1
    exact IsDomain.of_bot_isPrime S

end GroundTheory.Arith.SchemeCoh

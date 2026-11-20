import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
open IsLocalRing RingTheory.Sequence

namespace GlobalTheory.CompanionTheory.RegSeq

/- English proof (translation)
Set `W : Submodule (ResidueField R) (CotangentSpace R)` to `Submodule.span (ResidueField R) (Set.range (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R)))`. Set `c` to `Module.finBasis (ResidueField R) (CotangentSpace R ⧸ W)`. Establish `hsurj : ∀ q : CotangentSpace R ⧸ W, ∃ x : maximalIdeal R, W.mkQ ((maximalIdeal R).toCotangent x : CotangentSpace R) = q`. Introduce `q`. Take `⟨w, rfl⟩` from `W.mkQ_surjective q`.

Take `⟨x, rfl⟩` from `(maximalIdeal R).toCotangent_surjective w`. Conclude with `⟨x, rfl⟩`. Use `choose g hg using hsurj`. Set `s : Set (maximalIdeal R)` to `Set.range (fun i => (⟨f i, hf i⟩ : maximalIdeal R)) ∪ Set.range (fun j => g (c j))`. Set `T : Submodule (ResidueField R) (CotangentSpace R)` to `Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s)`.

Establish `hWT : W ≤ T`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `Submodule.subset_span ⟨⟨f i, hf i⟩, Or.inl ⟨i, rfl⟩, rfl⟩`. Establish `hT : T = ⊤`.

Establish `h1 : Submodule.map W.mkQ T = ⊤`. Rewrite using `[eq_top_iff, ← c.span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `⟨(maximalIdeal R).toCotangent (g (c j)), Submodule.subset_span ⟨g (c j), Or.inr ⟨j, rfl⟩, rfl⟩, hg _⟩`. Establish `h2` using `Submodule.comap_map_mkQ W T`.

Rewrite `h2` using `[h1, Submodule.comap_top]`. Rewrite using `[eq_top_iff, h2]`. Conclude with `sup_le hWT le_rfl`. Establish `hspan : Submodule.span R s = ⊤` using `IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hT`. Establish `hm : maximalIdeal R = Ideal.span (Subtype.val '' s)`.

Establish `h3` using `congrArg (Submodule.map (maximalIdeal R).subtype) hspan`. Rewrite `h3` using `[Submodule.map_span, Submodule.map_subtype_top, Submodule.coe_subtype]`. Conclude with `h3.symm`. Use `⟨List.ofFn (fun j => (g (c j)).val), ?_, ?_⟩` and prove the remaining obligations. Apply `le_antisymm` to reduce the goal to its premises.

Unfold `Ideal.ofList`. Rewrite using `[Ideal.span_le]`. Introduce `x hx`. Establish `hx' : x ∈ List.ofFn f ++ List.ofFn (fun j => (g (c j)).val)` using `hx`. Break down `List.mem_append.mp hx' with h | h` into its components or cases.

Take `⟨i, rfl⟩` from `List.mem_ofFn.mp h`. Conclude with `hf i`. Take `⟨j, rfl⟩` from `List.mem_ofFn.mp h`. Conclude with `(g (c j)).2`. Use `le_trans hm.le ?_` and prove the remaining obligations.

Unfold `Ideal.ofList`. Apply `Ideal.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx | hx, rfl⟩`. Take `⟨i, rfl⟩` from `hx`. Conclude with `List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)`.

Take `⟨j, rfl⟩` from `hx`. Conclude with `List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)`. Rewrite using `[List.length_append, List.length_ofFn, List.length_ofFn, IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]`. Establish `h1` using `Submodule.finrank_quotient_add_finrank W`. Establish `h2 : Module.finrank (ResidueField R) W = r`.

Simplify using `using finrank_span_eq_card hli`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_ofList_append_eq_maximalIdeal {R : Type} [CommRing R] [IsRegularLocalRing R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R))) :
    ∃ ys : List R, Ideal.ofList (List.ofFn f ++ ys) = maximalIdeal R ∧
      (List.ofFn f ++ ys).length = (maximalIdeal R).spanFinrank := by
  classical
  let W : Submodule (ResidueField R) (CotangentSpace R) :=
    Submodule.span (ResidueField R) (Set.range (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R)))
  let c := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ W)
  have hsurj : ∀ q : CotangentSpace R ⧸ W, ∃ x : maximalIdeal R,
      W.mkQ ((maximalIdeal R).toCotangent x : CotangentSpace R) = q := by
    intro q
    obtain ⟨w, rfl⟩ := W.mkQ_surjective q
    obtain ⟨x, rfl⟩ := (maximalIdeal R).toCotangent_surjective w
    exact ⟨x, rfl⟩
  choose g hg using hsurj
  let s : Set (maximalIdeal R) :=
    Set.range (fun i => (⟨f i, hf i⟩ : maximalIdeal R)) ∪ Set.range (fun j => g (c j))
  let T : Submodule (ResidueField R) (CotangentSpace R) :=
    Submodule.span (ResidueField R) ((maximalIdeal R).toCotangent '' s)
  have hWT : W ≤ T := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨⟨f i, hf i⟩, Or.inl ⟨i, rfl⟩, rfl⟩
  have hT : T = ⊤ := by
    have h1 : Submodule.map W.mkQ T = ⊤ := by
      rw [eq_top_iff, ← c.span_eq, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨(maximalIdeal R).toCotangent (g (c j)), Submodule.subset_span ⟨g (c j), Or.inr ⟨j, rfl⟩, rfl⟩, hg _⟩
    have h2 := Submodule.comap_map_mkQ W T
    rw [h1, Submodule.comap_top] at h2
    rw [eq_top_iff, h2]
    exact sup_le hWT le_rfl
  have hspan : Submodule.span R s = ⊤ := IsLocalRing.CotangentSpace.span_image_eq_top_iff.mp hT
  have hm : maximalIdeal R = Ideal.span (Subtype.val '' s) := by
    have h3 := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_subtype_top, Submodule.coe_subtype] at h3
    exact h3.symm
  refine ⟨List.ofFn (fun j => (g (c j)).val), ?_, ?_⟩
  · apply le_antisymm
    · unfold Ideal.ofList
      rw [Ideal.span_le]
      intro x hx
      have hx' : x ∈ List.ofFn f ++ List.ofFn (fun j => (g (c j)).val) := hx
      rcases List.mem_append.mp hx' with h | h
      · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp h
        exact hf i
      · obtain ⟨j, rfl⟩ := List.mem_ofFn.mp h
        exact (g (c j)).2
    · refine le_trans hm.le ?_
      unfold Ideal.ofList
      apply Ideal.span_mono
      rintro _ ⟨x, hx | hx, rfl⟩
      · obtain ⟨i, rfl⟩ := hx
        exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩)
      · obtain ⟨j, rfl⟩ := hx
        exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨j, rfl⟩)
  · rw [List.length_append, List.length_ofFn, List.length_ofFn,
      IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    have h1 := Submodule.finrank_quotient_add_finrank W
    have h2 : Module.finrank (ResidueField R) W = r := by
      simpa using finrank_span_eq_card hli
    omega

/- English proof (translation)
Take `⟨ys, h1, h2⟩` from `exists_ofList_append_eq_maximalIdeal f hf hli`. Conclude with `((isWeaklyRegular_append_iff R _ _).1 (GlobalTheory.isRegular_of_length_eq_spanFinrank h1 h2).toIsWeaklyRegular).1`.
-/
theorem isWeaklyRegular_ofFn {R : Type} [CommRing R] [IsRegularLocalRing R] {r : ℕ}
    (f : Fin r → R) (hf : ∀ i, f i ∈ maximalIdeal R)
    (hli : LinearIndependent (ResidueField R)
      (fun i => ((maximalIdeal R).toCotangent ⟨f i, hf i⟩ : CotangentSpace R))) :
    IsWeaklyRegular R (List.ofFn f) := by
  obtain ⟨ys, h1, h2⟩ := exists_ofList_append_eq_maximalIdeal f hf hli
  exact ((isWeaklyRegular_append_iff R _ _).1
    (GlobalTheory.isRegular_of_length_eq_spanFinrank h1 h2).toIsWeaklyRegular).1

/- English proof (translation)
Introduce `R _ _ _ _ d a hd hli`. Distinguish the cases in `hall : ∀ j, a j ∈ maximalIdeal R`. Establish `hli' : LinearIndependent (ResidueField R) (fun i => ((maximalIdeal R).toCotangent ⟨a i, hall i⟩ : CotangentSpace R))` using `hli.comp (fun i => ⟨i, hall i⟩) (fun i j h => congrArg Subtype.val h)`. Use `⟨isWeaklyRegular_ofFn a hall hli', ?_⟩` and prove the remaining obligations. Take `⟨ys, h1, h2⟩` from `exists_ofList_append_eq_maximalIdeal a hall hli'`.

Establish `hsf : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R` using `IsRegularLocalRing.spanFinrank_maximalIdeal`. Establish `hle : (maximalIdeal R).spanFinrank ≤ d`. Establish `h3` using `hsf.trans_le hd`. Conclude with `h3` after adjusting the coercions. Establish `hys : ys = []`.

Rewrite `h2` using `[List.length_append, List.length_ofFn]`. Apply `List.eq_nil_of_length_eq_zero` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Substitute `hys` using the available equality. Rewrite `h1` using `[List.append_nil]`.

Establish `hspan : Ideal.span (Set.range a) = maximalIdeal R`. Rewrite using `[← h1]`. Unfold `Ideal.ofList`. Use `congr 1`. Use extensionality with `x`.

Conclude with `List.mem_ofFn.symm`. Rewrite using `[hspan]`. Establish `hs : IsSimpleModule R (R ⧸ maximalIdeal R)` using `isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))`. Conclude with `(Module.length_eq_one_iff.mpr hs).le`. Use `push_neg at hall`.

Take `⟨j1, hj1⟩` from `hall`. Establish `hex : ∃ n, ∃ h : n < d, a ⟨n, h⟩ ∉ maximalIdeal R` using `⟨j1.val, j1.isLt, hj1⟩`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn, han, hmin⟩ : ∃ n, ∃ hn : n < d, a ⟨n, hn⟩ ∉ maximalIdeal R ∧ ∀ k (hk : k < n), a ⟨k, lt_trans hk hn⟩ ∈ maximalIdeal R := by`. Use `⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`.

Conclude with `Nat.find_min hex hk ⟨lt_trans hk (Nat.find_spec hex).1, hc⟩`. Establish `hu : IsUnit (a ⟨n, hn⟩)`. Assume the negation of the conclusion as `h`. Conclude with `han ((mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))`. Establish `htop : ∀ i, n < i → Ideal.ofList ((List.ofFn a).take i) = ⊤`.

Introduce `i hi`. Apply `Ideal.eq_top_of_isUnit_mem _ _ hu` to reduce the goal to its premises. Apply `Ideal.subset_span` to reduce the goal to its premises. Use `show a ⟨n, hn⟩ ∈ (List.ofFn a).take i`. Use `List.mem_take_iff_getElem.mpr ⟨n, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[List.length_ofFn]`. Conclude with `lt_min hi hn`. Rewrite using `[List.getElem_ofFn]`. Establish `hsub : ∀ (N : Submodule R R), N = ⊤ → ∀ r : R, IsSMulRegular (R ⧸ N) r`. Introduce and unpack `N rfl r x y _`.

Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Conclude with `(Submodule.Quotient.eq _).2 Submodule.mem_top`. Establish `hpre : IsWeaklyRegular R (List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩))` using `isWeaklyRegular_ofFn _ (fun k => hmin k k.2) (hli.comp (fun k : Fin n => ⟨⟨k, lt_trans k.2 hn⟩, hmin k k.2⟩) (fun x y h => by`. Establish `h5` using `congrArg (fun z : {j : Fin d // a j ∈ maximalIdeal R} => (z.1 : Fin d).val) h`.

Conclude with `Fin.ext h5))`. Establish `hpre' : List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩) = (List.ofFn a).take n`. Apply `List.ext_getElem` to reduce the goal to its premises. Simplify using `only [List.length_ofFn, List.length_take]`. Use linear arithmetic over natural numbers and integers.

Introduce `i h1 h2`. Simplify using `[List.getElem_ofFn, List.getElem_take]`. Use `⟨(isWeaklyRegular_iff R _).2 (fun i hi => ?_), ?_⟩` and prove the remaining obligations. Rewrite `hi` using `[List.length_ofFn]`. Break down `lt_trichotomy i n with h | h | h` into its components or cases.

Establish `hg` using `(isWeaklyRegular_iff R _).1 hpre i (by rw [List.length_ofFn]; exact h)`. Establish `e1 : (List.ofFn a).take i = (List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩)).take i`. Rewrite using `[hpre', List.take_take, min_eq_left h.le]`. Rewrite using `[e1]`. Simplify using `only [List.getElem_ofFn] at hg ⊢`.

Conclude with `hg`. Substitute `h` using the available equality. Simplify using `only [List.getElem_ofFn]`. Conclude with `IsUnit.isSMulRegular _ hu`. Conclude with `hsub _ (by rw [htop i h, Submodule.top_smul]) _`.

Establish `hspan : Ideal.span (Set.range a) = ⊤` using `Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨n, hn⟩, rfl⟩) hu`. Rewrite using `[hspan]`. Establish `hss : Subsingleton (R ⧸ (⊤ : Ideal R))` using `Ideal.Quotient.subsingleton_iff.mpr rfl`. Rewrite using `[Module.length_eq_zero_iff.mpr hss]`. Conclude with `zero_le_one`.
-/
theorem isWeaklyRegular_and_length_quotient_le_one :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] (d : ℕ)
      (a : Fin d → R), ringKrullDim R ≤ d →
      LinearIndependent (ResidueField R) (fun j : {j : Fin d // a j ∈ maximalIdeal R} =>
        ((maximalIdeal R).toCotangent ⟨_, j.2⟩ : CotangentSpace R)) →
      RingTheory.Sequence.IsWeaklyRegular R (List.ofFn a) ∧
        Module.length R (R ⧸ Ideal.span (Set.range a)) ≤ 1 := by
  intro R _ _ _ _ d a hd hli
  classical
  by_cases hall : ∀ j, a j ∈ maximalIdeal R
  · have hli' : LinearIndependent (ResidueField R)
        (fun i => ((maximalIdeal R).toCotangent ⟨a i, hall i⟩ : CotangentSpace R)) :=
      hli.comp (fun i => ⟨i, hall i⟩) (fun i j h => congrArg Subtype.val h)
    refine ⟨isWeaklyRegular_ofFn a hall hli', ?_⟩
    obtain ⟨ys, h1, h2⟩ := exists_ofList_append_eq_maximalIdeal a hall hli'
    have hsf : ((maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    have hle : (maximalIdeal R).spanFinrank ≤ d := by
      have h3 := hsf.trans_le hd
      exact_mod_cast h3
    have hys : ys = [] := by
      rw [List.length_append, List.length_ofFn] at h2
      apply List.eq_nil_of_length_eq_zero
      omega
    subst hys
    rw [List.append_nil] at h1
    have hspan : Ideal.span (Set.range a) = maximalIdeal R := by
      rw [← h1]
      unfold Ideal.ofList
      congr 1
      ext x
      exact List.mem_ofFn.symm
    rw [hspan]
    have hs : IsSimpleModule R (R ⧸ maximalIdeal R) :=
      isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp (maximalIdeal.isMaximal R))
    exact (Module.length_eq_one_iff.mpr hs).le
  · push_neg at hall
    obtain ⟨j1, hj1⟩ := hall
    have hex : ∃ n, ∃ h : n < d, a ⟨n, h⟩ ∉ maximalIdeal R := ⟨j1.val, j1.isLt, hj1⟩
    obtain ⟨n, hn, han, hmin⟩ : ∃ n, ∃ hn : n < d, a ⟨n, hn⟩ ∉ maximalIdeal R ∧
        ∀ k (hk : k < n), a ⟨k, lt_trans hk hn⟩ ∈ maximalIdeal R := by
      refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, fun k hk => ?_⟩
      by_contra hc
      exact Nat.find_min hex hk ⟨lt_trans hk (Nat.find_spec hex).1, hc⟩
    have hu : IsUnit (a ⟨n, hn⟩) := by
      by_contra h
      exact han ((mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))
    have htop : ∀ i, n < i → Ideal.ofList ((List.ofFn a).take i) = ⊤ := by
      intro i hi
      apply Ideal.eq_top_of_isUnit_mem _ _ hu
      apply Ideal.subset_span
      show a ⟨n, hn⟩ ∈ (List.ofFn a).take i
      refine List.mem_take_iff_getElem.mpr ⟨n, ?_, ?_⟩
      · rw [List.length_ofFn]
        exact lt_min hi hn
      · rw [List.getElem_ofFn]
    have hsub : ∀ (N : Submodule R R), N = ⊤ → ∀ r : R, IsSMulRegular (R ⧸ N) r := by
      rintro N rfl r x y _
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top
    have hpre : IsWeaklyRegular R (List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩)) :=
      isWeaklyRegular_ofFn _ (fun k => hmin k k.2)
        (hli.comp (fun k : Fin n => ⟨⟨k, lt_trans k.2 hn⟩, hmin k k.2⟩) (fun x y h => by
          have h5 := congrArg (fun z : {j : Fin d // a j ∈ maximalIdeal R} => (z.1 : Fin d).val) h
          exact Fin.ext h5))
    have hpre' : List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩) = (List.ofFn a).take n := by
      apply List.ext_getElem
      · simp only [List.length_ofFn, List.length_take]
        omega
      · intro i h1 h2
        simp [List.getElem_ofFn, List.getElem_take]
    refine ⟨(isWeaklyRegular_iff R _).2 (fun i hi => ?_), ?_⟩
    · rw [List.length_ofFn] at hi
      rcases lt_trichotomy i n with h | h | h
      · have hg := (isWeaklyRegular_iff R _).1 hpre i (by rw [List.length_ofFn]; exact h)
        have e1 : (List.ofFn a).take i =
            (List.ofFn (fun k : Fin n => a ⟨k, lt_trans k.2 hn⟩)).take i := by
          rw [hpre', List.take_take, min_eq_left h.le]
        rw [e1]
        simp only [List.getElem_ofFn] at hg ⊢
        exact hg
      · subst h
        simp only [List.getElem_ofFn]
        exact IsUnit.isSMulRegular _ hu
      · exact hsub _ (by rw [htop i h, Submodule.top_smul]) _
    · have hspan : Ideal.span (Set.range a) = ⊤ :=
        Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨⟨n, hn⟩, rfl⟩) hu
      rw [hspan]
      have hss : Subsingleton (R ⧸ (⊤ : Ideal R)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      rw [Module.length_eq_zero_iff.mpr hss]
      exact zero_le_one

end GlobalTheory.CompanionTheory.RegSeq

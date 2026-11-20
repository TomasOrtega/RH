import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KisinCrTrivial
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.nakayama
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PointFinitePower
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Published IsLocalRing Polynomial

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x)` using `rfl`. Rewrite using `[h0, spectralValue_le_one_iff (minpoly.monic hi)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]`. Conclude with `PadicInt.norm_le_one _`. Introduce `h`. Establish `hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l])` using `(lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
private theorem ptFin_int {l : ℕ} [Fact l.Prime] (x : PadicAlgCl l) : IsIntegral ℤ_[l] x ↔ ‖x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖x‖ = spectralValue (minpoly ℚ_[l] x) := rfl
  rw [h0, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by rw [← aeval_def, ← aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow m hres n`.
-/
private theorem ptFin_pow {O S : Type} [CommRing O] [CommRing S] [Algebra O S] [IsNoetherianRing S] (m : Ideal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ m) (n : ℕ) :
    ∃ N : Submodule O S, N.FG ∧ ∀ x : S, ∃ y ∈ N, x - y ∈ m ^ n :=
  _root_.UpperTheory.Reformulated.B.PointFinitePower.ptFin_pow m hres n

/- English proof (translation)
Use `set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ`. Establish `hJle : J ≤ maximalIdeal S` using `Ideal.map_le_iff_le_comap.2 hloc`. Establish `hJne : J ≠ ⊤` using `fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))`. Use `haveI : IsHausdorff (maximalIdeal O) S := IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)`. Establish `hrad : maximalIdeal S ≤ J.radical`.

Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf ?_` and prove the remaining obligations. Introduce and unpack `P ⟨hJP, hP⟩`. Establish `h1 : maximalIdeal O ≤ P.comap (algebraMap O S)` using `Ideal.map_le_iff_le_comap.1 hJP`. Establish `h2 : P.comap (algebraMap O S) = maximalIdeal O` using `((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm`.

Establish `h3 : P.IsMaximal` using `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) P (h2 ▸ maximalIdeal.isMaximal O)`. Conclude with `(eq_maximalIdeal h3).ge`. Take `⟨n, hn⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)`. Take `⟨N, hN, h⟩` from `ptFin_pow (maximalIdeal S) hres n`. Use `(UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩` and prove the remaining obligations.

Establish `: (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _)`. Use `symm`. Rewrite using `[Submodule.map_mkQ_eq_top, eq_top_iff]`. Introduce `x _`. Take `⟨y, hy, h1⟩` from `h x`.

Establish `h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S)`. Rewrite using `[Ideal.smul_top_eq_map]`. Conclude with `hn h1`. Simplify using `using Submodule.add_mem_sup h2 hy`. Rewrite using `[this]`.

Conclude with `hN.map _`.
-/
private theorem ptFin_finite {O S : Type} [CommRing O] [IsLocalRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing S] [Algebra O S] [IsLocalRing S] [IsNoetherianRing S] [Algebra.IsIntegral O S]
    (hloc : ∀ a ∈ maximalIdeal O, algebraMap O S a ∈ maximalIdeal S)
    (hres : ∀ x : S, ∃ a : O, x - algebraMap O S a ∈ maximalIdeal S) : Module.Finite O S := by
  set J : Ideal S := (maximalIdeal O).map (algebraMap O S) with hJ
  have hJle : J ≤ maximalIdeal S := Ideal.map_le_iff_le_comap.2 hloc
  have hJne : J ≠ ⊤ := fun h => (maximalIdeal.isMaximal S).ne_top (top_le_iff.1 (h ▸ hJle))
  haveI : IsHausdorff (maximalIdeal O) S :=
    IsHausdorff.map_algebraMap_iff.1 (IsHausdorff.of_isLocalRing J S hJne)
  have hrad : maximalIdeal S ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    have h1 : maximalIdeal O ≤ P.comap (algebraMap O S) := Ideal.map_le_iff_le_comap.1 hJP
    have h2 : P.comap (algebraMap O S) = maximalIdeal O :=
      ((maximalIdeal.isMaximal O).eq_of_le (Ideal.comap_ne_top _ hP.ne_top) h1).symm
    have h3 : P.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := O) P
      (h2 ▸ maximalIdeal.isMaximal O)
    exact (eq_maximalIdeal h3).ge
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  obtain ⟨N, hN, h⟩ := ptFin_pow (maximalIdeal S) hres n
  refine (UpperTheory.V.abelian₂.nakayama O (maximalIdeal O) S).2 ⟨?_⟩
  have : (⊤ : Submodule O (S ⧸ (maximalIdeal O) • (⊤ : Submodule O S))) = N.map (Submodule.mkQ _) := by
    symm
    rw [Submodule.map_mkQ_eq_top, eq_top_iff]
    intro x _
    obtain ⟨y, hy, h1⟩ := h x
    have h2 : x - y ∈ (maximalIdeal O) • (⊤ : Submodule O S) := by
      rw [Ideal.smul_top_eq_map]
      exact hn h1
    simpa using Submodule.add_mem_sup h2 hy
  rw [this]
  exact hN.map _

/- English proof (translation)
Introduce `l _ O _ _ _ _ _ _ _ _ _ R _ _ _ F hF`. Use `set f := dualFst F with hf`. Establish `hfa : ∀ a, (F a).fst = f a` using `fun a => rfl`. Establish `hO : ∀ a : O, IsIntegral ℤ_[l] (algebraMap O (PadicAlgCl l) a)` using `fun a => (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l))`. Establish `hint : ∀ a : R, IsIntegral O (f a)`.

Introduce `a`. Take `⟨c, hc⟩` from `IsCO.res_surj (O := O) a`. Establish `h1 : IsIntegral O (f (a - algebraMap O R c))` using `((ptFin_int _).2 (hF _ hc).le).tower_top`. Establish `h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c` using `by simp`. Rewrite using `[h2]`.

Conclude with `h1.add isIntegral_algebraMap`. Set `g : R →ₐ[O] f.range` to `f.rangeRestrict`. Establish `hg : Function.Surjective g` using `f.rangeRestrict_surjective`. Use `haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg`. Use `haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg`.

Use `haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg`. Establish `hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range` using `fun a ha => map_nonunit (g : R →+* f.range) a ha`. Use `haveI : Algebra.IsIntegral O f.range := ⟨fun x => by`. Take `⟨a, rfl⟩` from `hg x`. Conclude with `(isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩`.

Use `haveI : Module.Finite O f.range := ptFin_finite (fun a ha => by`. Rewrite using `[← g.commutes]`. Conclude with `hm _ (map_nonunit (algebraMap O R) a ha))`. Use the proof step `(fun x => by`. Take `⟨a, rfl⟩` from `hg x`.

Take `⟨c, hc⟩` from `IsCO.res_surj (O := O) a`. Conclude with `⟨c, by simpa using hm _ hc⟩)`. Take `⟨r, s, hs⟩` from `Module.Finite.exists_fin (R := O) (M := f.range)`. Use `choose b hb using fun i => hg (s i)`. Take `⟨r', o, ho⟩` from `Module.Finite.exists_fin (R := ℤ_[l]) (M := O)`.

Take `⟨P, hP⟩ : (RingHom.ker f).FG` from `IsNoetherian.noetherian _`. Set `T : Set (PadicAlgCl l)` to `Set.range (fun i => algebraMap O (PadicAlgCl l) (o i)) ∪ Set.range (fun i => f (b i)) ∪ Set.range (fun i => (F (b i)).snd) ∪ (fun p => (F p).snd) '' (P : Set R)`. Establish `hT : T.Finite` using `(((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union (P.finite_toSet.image _)`. Use `haveI : Finite T := hT`. Set `E : IntermediateField ℚ_[l] (PadicAlgCl l)` to `IntermediateField.adjoin ℚ_[l] T`.

Establish `hE : FiniteDimensional ℚ_[l] E` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Establish `hTE : T ⊆ E` using `IntermediateField.subset_adjoin _ _`. Establish `hOE : ∀ c : O, algebraMap O (PadicAlgCl l) c ∈ E`. Introduce `c`. Establish `hc : c ∈ Submodule.span ℤ_[l] (Set.range o)` using `ho ▸ Submodule.mem_top`.

Take `⟨u, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hc`. Rewrite using `[map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]`. Conclude with `mul_mem (E.algebraMap_mem _) (hTE (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))`.

Establish `hdec : ∀ a : R, ∃ u : Fin r → O, a - ∑ i, u i • b i ∈ RingHom.ker f`. Introduce `a`. Establish `hc : g a ∈ Submodule.span O (Set.range s)` using `hs ▸ Submodule.mem_top`. Take `⟨u, hu⟩` from `(Submodule.mem_span_range_iff_exists_fun _).1 hc`. Use `⟨u, ?_⟩` and prove the remaining obligations.

Establish `h1 : g (a - ∑ i, u i • b i) = 0` using `by simp [hb, hu]`. Conclude with `congrArg Subtype.val h1`. Establish `h1 : ∀ a, f a ∈ E`. Introduce `a`. Take `⟨u, hu⟩` from `hdec a`.

Rewrite `hu` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`. Rewrite using `[hu, map_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Algebra.smul_def]`. Conclude with `mul_mem (hOE _) (hTE (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))`.

Establish `h2 : ∀ a ∈ Ideal.span (P : Set R), (F a).snd ∈ E`. Introduce `a ha`. Proceed by induction on `ha using Submodule.span_induction with`. Consider the case `mem z hz => exact hTE (Or.inr ⟨z, hz, rfl⟩)`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, TrivSqZeroExt.snd_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x hx0 hx`. Establish `h0 : (F x).fst = 0`. Establish `: x ∈ RingHom.ker f` using `hP ▸ hx0`.

Conclude with `this`. Rewrite using `[smul_eq_mul, map_mul, DualNumber.snd_mul, h0, mul_zero, add_zero]`. Conclude with `mul_mem (h1 c) hx`. Use `⟨⟨E, hE⟩, fun a => ⟨h1 a, ?_⟩⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hdec a`.

Establish `h3` using `h2 _ (hP ▸ hu)`. Establish `h4 : (F (∑ i, u i • b i)).snd ∈ E`. Rewrite using `[map_sum, TrivSqZeroExt.snd_sum]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, TrivSqZeroExt.snd_smul, Algebra.smul_def]`.

Conclude with `mul_mem (hOE _) (hTE (Or.inl (Or.inr ⟨i, rfl⟩)))`. Establish `h5` using `add_mem h3 h4`. Rewrite `h5` using `[← TrivSqZeroExt.snd_add, ← map_add, sub_add_cancel]`. Then use the resulting hypothesis.
-/
theorem UpperTheory.V.Loc.ptFin :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] [Algebra O (PadicAlgCl l)] [IsScalarTower ℤ_[l] O (PadicAlgCl l)] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (F : R →ₐ[O] DualNumber (PadicAlgCl l)), IsLocPt (dualFst F) → ∃ E' : FinExt l, ∀ a, (F a).fst ∈ E'.1 ∧ (F a).snd ∈ E'.1 := by
  intro l _ O _ _ _ _ _ _ _ _ _ R _ _ _ F hF
  classical
  set f := dualFst F with hf
  have hfa : ∀ a, (F a).fst = f a := fun a => rfl
  have hO : ∀ a : O, IsIntegral ℤ_[l] (algebraMap O (PadicAlgCl l) a) := fun a =>
    (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) a).map (IsScalarTower.toAlgHom ℤ_[l] O (PadicAlgCl l))
  have hint : ∀ a : R, IsIntegral O (f a) := by
    intro a
    obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
    have h1 : IsIntegral O (f (a - algebraMap O R c)) := ((ptFin_int _).2 (hF _ hc).le).tower_top
    have h2 : f a = f (a - algebraMap O R c) + algebraMap O _ c := by simp
    rw [h2]
    exact h1.add isIntegral_algebraMap
  let g : R →ₐ[O] f.range := f.rangeRestrict
  have hg : Function.Surjective g := f.rangeRestrict_surjective
  haveI : IsLocalRing f.range := IsLocalRing.of_surjective' (g : R →+* f.range) hg
  haveI : IsNoetherianRing f.range := isNoetherianRing_of_surjective R _ (g : R →+* f.range) hg
  haveI : IsLocalHom (g : R →+* f.range) := IsLocalHom.of_surjective _ hg
  have hm : ∀ a ∈ maximalIdeal R, g a ∈ maximalIdeal f.range := fun a ha =>
    map_nonunit (g : R →+* f.range) a ha
  haveI : Algebra.IsIntegral O f.range := ⟨fun x => by
    obtain ⟨a, rfl⟩ := hg x
    exact (isIntegral_algHom_iff f.range.val Subtype.val_injective).1 (hint a)⟩
  haveI : Module.Finite O f.range := ptFin_finite
    (fun a ha => by
      rw [← g.commutes]
      exact hm _ (map_nonunit (algebraMap O R) a ha))
    (fun x => by
      obtain ⟨a, rfl⟩ := hg x
      obtain ⟨c, hc⟩ := IsCO.res_surj (O := O) a
      exact ⟨c, by simpa using hm _ hc⟩)
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := f.range)
  choose b hb using fun i => hg (s i)
  obtain ⟨r', o, ho⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := O)
  obtain ⟨P, hP⟩ : (RingHom.ker f).FG := IsNoetherian.noetherian _
  let T : Set (PadicAlgCl l) := Set.range (fun i => algebraMap O (PadicAlgCl l) (o i)) ∪ Set.range (fun i => f (b i)) ∪
    Set.range (fun i => (F (b i)).snd) ∪ (fun p => (F p).snd) '' (P : Set R)
  have hT : T.Finite :=
    (((Set.finite_range _).union (Set.finite_range _)).union (Set.finite_range _)).union (P.finite_toSet.image _)
  haveI : Finite T := hT
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := IntermediateField.adjoin ℚ_[l] T
  have hE : FiniteDimensional ℚ_[l] E :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hTE : T ⊆ E := IntermediateField.subset_adjoin _ _
  have hOE : ∀ c : O, algebraMap O (PadicAlgCl l) c ∈ E := by
    intro c
    have hc : c ∈ Submodule.span ℤ_[l] (Set.range o) := ho ▸ Submodule.mem_top
    obtain ⟨u, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
    rw [map_sum]
    refine sum_mem fun i _ => ?_
    rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
    exact mul_mem (E.algebraMap_mem _) (hTE (Or.inl (Or.inl (Or.inl ⟨i, rfl⟩))))
  have hdec : ∀ a : R, ∃ u : Fin r → O, a - ∑ i, u i • b i ∈ RingHom.ker f := by
    intro a
    have hc : g a ∈ Submodule.span O (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨u, hu⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hc
    refine ⟨u, ?_⟩
    have h1 : g (a - ∑ i, u i • b i) = 0 := by simp [hb, hu]
    exact congrArg Subtype.val h1
  have h1 : ∀ a, f a ∈ E := by
    intro a
    obtain ⟨u, hu⟩ := hdec a
    rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hu
    rw [hu, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, Algebra.smul_def]
    exact mul_mem (hOE _) (hTE (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))
  have h2 : ∀ a ∈ Ideal.span (P : Set R), (F a).snd ∈ E := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem z hz => exact hTE (Or.inr ⟨z, hz, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, TrivSqZeroExt.snd_add]; exact add_mem hx hy
    | smul c x hx0 hx =>
      have h0 : (F x).fst = 0 := by
        have : x ∈ RingHom.ker f := hP ▸ hx0
        exact this
      rw [smul_eq_mul, map_mul, DualNumber.snd_mul, h0, mul_zero, add_zero]
      exact mul_mem (h1 c) hx
  refine ⟨⟨E, hE⟩, fun a => ⟨h1 a, ?_⟩⟩
  obtain ⟨u, hu⟩ := hdec a
  have h3 := h2 _ (hP ▸ hu)
  have h4 : (F (∑ i, u i • b i)).snd ∈ E := by
    rw [map_sum, TrivSqZeroExt.snd_sum]
    refine sum_mem fun i _ => ?_
    rw [map_smul, TrivSqZeroExt.snd_smul, Algebra.smul_def]
    exact mul_mem (hOE _) (hTE (Or.inl (Or.inr ⟨i, rfl⟩)))
  have h5 := add_mem h3 h4
  rwa [← TrivSqZeroExt.snd_add, ← map_add, sub_add_cancel] at h5

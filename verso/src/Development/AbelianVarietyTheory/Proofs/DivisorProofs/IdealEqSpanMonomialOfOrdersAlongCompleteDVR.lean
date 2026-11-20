import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtOfToricChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfMemAdjoinInv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGenOfFrames

noncomputable section

open IsLocalRing GlobalTheory.Toroidal

namespace GlobalTheory.MonoVal

/- English proof (translation)
Use `set q : ChartRing k m e := ∏ i, bdParam k m e i ^ a i with hqdef`. Use `haveI : CharZero (ChartRing k m e) := (MvPowerSeries.constantCoeff : ChartRing k m e →+* k).charZero`. Take `⟨hN, hIC, -, -⟩` from `GlobalTheory.ChartCone.isCN_chartRing k m e`. Use `haveI := hN`. Use `haveI := hIC`.

Establish `hX : ∀ j : Fin m ⊕ Fin e, (MvPowerSeries.X j : ChartRing k m e) ≠ 0`. Introduce `j hj`. Use `congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) hj` as an intermediate fact. Simplify using `[MvPowerSeries.coeff_X] at this`. Establish `hq0 : q ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hX _)`.

Establish `loc_of : ∀ {V : Type} [CommRing V] [IsLocalRing V] (φ : ChartRing k m e →+* V), (maximalIdeal V).comap φ = maximalIdeal (ChartRing k m e) → IsLocalHom φ`. Introduce `V _ _ φ hφ`. Use `⟨fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnu`. Establish `hx' : x ∈ maximalIdeal (ChartRing k m e)` using `hnu`.

Rewrite `hx'` using `[← hφ, Ideal.mem_comap]`. Conclude with `hx' hx`. Establish `hle : I ≤ Ideal.span {q}`. Introduce `f hf`. Rewrite using `[Ideal.mem_span_singleton]`.

Use `GlobalTheory.ValCrit.dvd_of_forall_cdvr _ f q hq0 fun V _ _ _ φ hV hinj hφ => ?_` and prove the remaining obligations. Establish `hm` using `h V hV φ hinj (loc_of φ hφ)`. Rewrite using `[← Ideal.mem_span_singleton, ← hm]`. Conclude with `Ideal.mem_map_of_mem φ hf`. Use `le_antisymm hle ?_` and prove the remaining obligations.

Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Assume the negation of the conclusion as `hqI`. Set `I' : Ideal (ChartRing k m e)` to `Submodule.comap (LinearMap.mulLeft (ChartRing k m e) q) I`. Establish `hmemI' : ∀ g, g ∈ I' ↔ q * g ∈ I` using `fun g => Iff.rfl`. Establish `key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ψ : ChartRing k m e →+* V), GlobalTheory.LN.CDvr V → Function.Injective ψ → IsLocalHom ψ → False`.

Introduce `V _ _ _ ψ hV hinj hψ`. Establish `hmap` using `h V hV ψ hinj hψ`. Establish `hI : I = Ideal.span {q} * I'`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`.

Take `⟨g, rfl⟩` from `Ideal.mem_span_singleton'.1 (hle hf)`. Conclude with `Ideal.mem_span_singleton_mul.2 ⟨g, (hmemI' g).2 (by rwa [mul_comm]), mul_comm _ _⟩`. Rewrite using `[Ideal.span_singleton_mul_le_iff]`. Introduce `z hz`. Conclude with `(hmemI' z).1 hz`.

Establish `hψq : ψ q ≠ 0` using `(map_ne_zero_iff ψ hinj).2 hq0`. Establish `htop : Ideal.map ψ I' = ⊤`. Establish `h2 : Ideal.span {ψ q} * Ideal.map ψ I' = Ideal.span {ψ q} * ⊤`. Establish `h3 : Ideal.map ψ (Ideal.span {q} * I') = Ideal.span {ψ q} * Ideal.map ψ I'`. Rewrite using `[Ideal.map_mul, Ideal.map_span, Set.image_singleton]`.

Rewrite using `[Ideal.mul_top, ← h3, ← hI, hmap]`. Conclude with `(Ideal.span_singleton_mul_right_inj hψq).1 h2`. Establish `hI'ne : I' ≠ ⊤`. Introduce `ht`. Apply `hqI` to reduce the goal to its premises.

Establish `h1 : (1 : ChartRing k m e) ∈ I'` using `ht ▸ Submodule.mem_top`. Simplify using `using (hmemI' 1).1 h1`. Establish `hle' : Ideal.map ψ I' ≤ maximalIdeal V`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`.

Establish `hx'` using `IsLocalRing.le_maximalIdeal hI'ne hx`. Rewrite `hx'` using `[mem_maximalIdeal, mem_nonunits_iff]`. Rewrite using `[Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]`. Conclude with `fun hu => hx' (isUnit_of_map_unit ψ x hu)`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal V).ne_top (top_le_iff.1 (htop ▸ hle'))`.

Break down `isEmpty_or_nonempty (Fin m ⊕ Fin e) with hσ | hne` into its components or cases. Set `ψ0 : ChartRing k m e →+* PowerSeries k` to `(PowerSeries.C : k →+* PowerSeries k).comp (MvPowerSeries.constantCoeff : ChartRing k m e →+* k)`. Establish `hc : ∀ f : ChartRing k m e, f = MvPowerSeries.C (MvPowerSeries.constantCoeff f)`. Introduce `f`. Use extensionality with `n`.

Establish `hn : n = 0` using `Subsingleton.elim _ _`. Substitute `hn` using the available equality. Simplify using the standard rewrite rules. Establish `hinj : Function.Injective ψ0`. Introduce `f g hfg`.

Establish `h1 : MvPowerSeries.constantCoeff f = MvPowerSeries.constantCoeff g`. Simplify `congrArg PowerSeries.constantCoeff hfg` using `[ψ0]`. Rewrite using `[hc f, hc g, h1]`. Establish `hloc : IsLocalHom ψ0`. Use `⟨fun f hf => ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPowerSeries.isUnit_iff_constantCoeff]`. Establish `h1 : IsUnit (PowerSeries.constantCoeff (ψ0 f))` using `hf.map _`. Simplify `h1` using `[ψ0]`. Conclude with `key (PowerSeries k) ψ0 (GlobalTheory.FrameGen.cDvr_powerSeries k) hinj hloc`. Take `⟨j⟩` from `hne`.

Establish `hdvd : (MvPowerSeries.X j : ChartRing k m e) ∣ 1` using `GlobalTheory.ValCrit.dvd_of_forall_cdvr _ 1 _ (hX j) fun V _ _ _ φ hV hinj hφ => (key V φ hV hinj (loc_of φ hφ)).elim`. Establish `hu` using `isUnit_of_dvd_one hdvd`. Rewrite `hu` using `[MvPowerSeries.isUnit_iff_constantCoeff]`. Simplify using `at hu`.
-/
theorem eq_span_monomial_of_forall_cdvr (k : Type) [Field k] [CharZero k] (m e : ℕ) (I : Ideal (ChartRing k m e))
    (a : Fin m → ℕ)
    (h : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ ψ : ChartRing k m e →+* W,
      Function.Injective ψ → IsLocalHom ψ → I.map ψ = Ideal.span {ψ (∏ i, bdParam k m e i ^ a i)}) :
    I = Ideal.span {∏ i, bdParam k m e i ^ a i} := by
  set q : ChartRing k m e := ∏ i, bdParam k m e i ^ a i with hqdef
  haveI : CharZero (ChartRing k m e) := (MvPowerSeries.constantCoeff : ChartRing k m e →+* k).charZero
  obtain ⟨hN, hIC, -, -⟩ := GlobalTheory.ChartCone.isCN_chartRing k m e
  haveI := hN
  haveI := hIC
  have hX : ∀ j : Fin m ⊕ Fin e, (MvPowerSeries.X j : ChartRing k m e) ≠ 0 := by
    intro j hj
    have := congrArg (MvPowerSeries.coeff (Finsupp.single j 1)) hj
    simp [MvPowerSeries.coeff_X] at this
  have hq0 : q ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hX _)
  have loc_of : ∀ {V : Type} [CommRing V] [IsLocalRing V] (φ : ChartRing k m e →+* V),
      (maximalIdeal V).comap φ = maximalIdeal (ChartRing k m e) → IsLocalHom φ := by
    intro V _ _ φ hφ
    refine ⟨fun x hx => ?_⟩
    by_contra hnu
    have hx' : x ∈ maximalIdeal (ChartRing k m e) := hnu
    rw [← hφ, Ideal.mem_comap] at hx'
    exact hx' hx

  have hle : I ≤ Ideal.span {q} := by
    intro f hf
    rw [Ideal.mem_span_singleton]
    refine GlobalTheory.ValCrit.dvd_of_forall_cdvr _ f q hq0 fun V _ _ _ φ hV hinj hφ => ?_
    have hm := h V hV φ hinj (loc_of φ hφ)
    rw [← Ideal.mem_span_singleton, ← hm]
    exact Ideal.mem_map_of_mem φ hf
  refine le_antisymm hle ?_
  rw [Ideal.span_le, Set.singleton_subset_iff]
  by_contra hqI
  let I' : Ideal (ChartRing k m e) := Submodule.comap (LinearMap.mulLeft (ChartRing k m e) q) I
  have hmemI' : ∀ g, g ∈ I' ↔ q * g ∈ I := fun g => Iff.rfl
  have key : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ψ : ChartRing k m e →+* V),
      GlobalTheory.LN.CDvr V → Function.Injective ψ → IsLocalHom ψ → False := by
    intro V _ _ _ ψ hV hinj hψ
    have hmap := h V hV ψ hinj hψ
    have hI : I = Ideal.span {q} * I' := by
      apply le_antisymm
      · intro f hf
        obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 (hle hf)
        exact Ideal.mem_span_singleton_mul.2 ⟨g, (hmemI' g).2 (by rwa [mul_comm]), mul_comm _ _⟩
      · rw [Ideal.span_singleton_mul_le_iff]
        intro z hz
        exact (hmemI' z).1 hz
    have hψq : ψ q ≠ 0 := (map_ne_zero_iff ψ hinj).2 hq0
    have htop : Ideal.map ψ I' = ⊤ := by
      have h2 : Ideal.span {ψ q} * Ideal.map ψ I' = Ideal.span {ψ q} * ⊤ := by
        have h3 : Ideal.map ψ (Ideal.span {q} * I') = Ideal.span {ψ q} * Ideal.map ψ I' := by
          rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
        rw [Ideal.mul_top, ← h3, ← hI, hmap]
      exact (Ideal.span_singleton_mul_right_inj hψq).1 h2
    have hI'ne : I' ≠ ⊤ := by
      intro ht
      apply hqI
      have h1 : (1 : ChartRing k m e) ∈ I' := ht ▸ Submodule.mem_top
      simpa using (hmemI' 1).1 h1
    have hle' : Ideal.map ψ I' ≤ maximalIdeal V := by
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx' := IsLocalRing.le_maximalIdeal hI'ne hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx'
      rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
      exact fun hu => hx' (isUnit_of_map_unit ψ x hu)
    exact (IsLocalRing.maximalIdeal.isMaximal V).ne_top (top_le_iff.1 (htop ▸ hle'))
  rcases isEmpty_or_nonempty (Fin m ⊕ Fin e) with hσ | hne
  ·
    let ψ0 : ChartRing k m e →+* PowerSeries k :=
      (PowerSeries.C : k →+* PowerSeries k).comp (MvPowerSeries.constantCoeff : ChartRing k m e →+* k)
    have hc : ∀ f : ChartRing k m e, f = MvPowerSeries.C (MvPowerSeries.constantCoeff f) := by
      intro f
      ext n
      have hn : n = 0 := Subsingleton.elim _ _
      subst hn
      simp
    have hinj : Function.Injective ψ0 := by
      intro f g hfg
      have h1 : MvPowerSeries.constantCoeff f = MvPowerSeries.constantCoeff g := by
        simpa [ψ0] using congrArg PowerSeries.constantCoeff hfg
      rw [hc f, hc g, h1]
    have hloc : IsLocalHom ψ0 := by
      refine ⟨fun f hf => ?_⟩
      rw [MvPowerSeries.isUnit_iff_constantCoeff]
      have h1 : IsUnit (PowerSeries.constantCoeff (ψ0 f)) := hf.map _
      simpa [ψ0] using h1
    exact key (PowerSeries k) ψ0 (GlobalTheory.FrameGen.cDvr_powerSeries k) hinj hloc
  · obtain ⟨j⟩ := hne
    have hdvd : (MvPowerSeries.X j : ChartRing k m e) ∣ 1 :=
      GlobalTheory.ValCrit.dvd_of_forall_cdvr _ 1 _ (hX j) fun V _ _ _ φ hV hinj hφ =>
        (key V φ hV hinj (loc_of φ hφ)).elim
    have hu := isUnit_of_dvd_one hdvd
    rw [MvPowerSeries.isUnit_iff_constantCoeff] at hu
    simp at hu

end GlobalTheory.MonoVal

import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

/- English proof (translation)
Establish `ho : IsOpen {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c}`. Establish `h0` using `(Valued.isOpen_ball (P.adicCompletion L) ((Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).restrict c)).preimage (continuous_sub_left y)`. Simplify `h0` using `only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff]`. Establish `hy : y ∈ {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c}` using `by show Valued.v (y - y) < Valued.v c`. Rewrite using `[sub_self, map_zero]`.

Conclude with `(Valuation.pos_iff _).2 hc`. Take `⟨k, hk⟩` from `(IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L) (v := P)).exists_mem_open ho ⟨y, hy⟩`. Conclude with `⟨k, hk⟩`.
-/
theorem adicCompletion_exists_approx_lt (L : Type) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (y c : P.adicCompletion L) (hc : c ≠ 0) :
    ∃ k : L, Valued.v (y - algebraMap L (P.adicCompletion L) k) < Valued.v c := by
  have ho : IsOpen {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c} := by
    have h0 := (Valued.isOpen_ball (P.adicCompletion L)
      ((Valued.v : Valuation (P.adicCompletion L) (WithZero (Multiplicative ℤ))).restrict c)).preimage
        (continuous_sub_left y)
    simpa only [Set.preimage_ofPred_eq, Valuation.restrict_lt_iff] using h0
  have hy : y ∈ {z : P.adicCompletion L | Valued.v (y - z) < Valued.v c} := by
    show Valued.v (y - y) < Valued.v c
    rw [sub_self, map_zero]
    exact (Valuation.pos_iff _).2 hc
  obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) (K := L)
    (v := P)).exists_mem_open ho ⟨y, hy⟩
  exact ⟨k, hk⟩

/- English proof (translation)
The claim follows from `IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (v := P) k`.
-/
private lemma valued_v_algebraMap_adicCompletion_foundation (L : Type) [Field L] [NumberField L]
    (P : HeightOneSpectrum (𝓞 L)) (k : L) :
    Valued.v (algebraMap L (P.adicCompletion L) k) = P.valuation L k :=
  IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) (v := P) k

/- English proof (translation)
Take `⟨π, hπ⟩` from `P.valuation_exists_uniformizer L`. Establish `hπ0 : π ≠ 0`. Introduce `h`. Rewrite `hπ` using `[h, map_zero]`. Conclude with `WithZero.exp_ne_zero hπ.symm`.

Establish `hN0 : (N : L) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `hN1 : P.valuation L (N : L) ≤ 1`. Simplify using `using P.valuation_le_one (K := L) (N : 𝓞 L)`. Establish `he1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≤ 1`. Rewrite using `[← WithZero.exp_zero, WithZero.exp_le_exp]`.

Evaluate the numerical expressions. Use `set c := y * algebraMap L (P.adicCompletion L) ((N : L) * π) with hcdef`. Establish `hc : c ≠ 0` using `mul_ne_zero hy ((map_ne_zero _).2 (mul_ne_zero hN0 hπ0))`. Take `⟨k₀, hk₀⟩` from `adicCompletion_exists_approx_lt L P y c hc`. Establish `hvc : Valued.v c = Valued.v y * (P.valuation L (N : L) * WithZero.exp (-1 : ℤ))`.

Rewrite using `[hcdef, map_mul, valued_v_algebraMap_adicCompletion_foundation, map_mul, hπ]`. Establish `hlt : Valued.v (y - algebraMap L _ k₀) < Valued.v y`. Use `hk₀.trans_le ?_` and prove the remaining obligations. Rewrite using `[hvc]`. Conclude with `mul_le_of_le_one_right' (mul_le_one' hN1 he1)`.

Establish `hyk : P.valuation L k₀ = Valued.v y`. Rewrite using `[← valued_v_algebraMap_adicCompletion_foundation]`. Apply `Valuation.map_eq_of_sub_lt` to reduce the goal to its premises. Rewrite using `[Valuation.map_sub_swap]` and apply the resulting hypothesis. Establish `hk0 : k₀ ≠ 0`.

Introduce `h`. Rewrite `hyk` using `[h, map_zero]`. Conclude with `hy ((Valuation.zero_iff _).1 hyk.symm)`. Use `⟨Units.mk0 k₀ hk0, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mk0, hyk]`.

Rewrite using `[Units.val_mk0, hyk]`. Use `(hk₀.trans_eq hvc).le.trans ?_` and prove the remaining obligations. Rewrite using `[mul_comm (Valued.v y)]`. Use `gcongr ?_ * _`. Conclude with `mul_le_of_le_one_right' he1`.

Rewrite using `[Units.val_mk0, hyk]`. Use `(hk₀.trans_eq hvc).le.trans ?_` and prove the remaining obligations. Rewrite using `[mul_comm (Valued.v y)]`. Use `gcongr ?_ * _`. Conclude with `mul_le_of_le_one_left' hN1`.
-/
theorem adicCompletion_exists_unit_approx (L : Type) [Field L] [NumberField L] (N : ℕ) (hN : 0 < N)
    (P : HeightOneSpectrum (𝓞 L)) (y : P.adicCompletion L) (hy : y ≠ 0) :
    ∃ k : Lˣ, Valued.v y = P.valuation L (k : L) ∧
      Valued.v (y - algebraMap L _ (k : L)) ≤ P.valuation L (N : L) * P.valuation L (k : L) ∧
      Valued.v (y - algebraMap L _ (k : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k : L) := by
  obtain ⟨π, hπ⟩ := P.valuation_exists_uniformizer L
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hN0 : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hN1 : P.valuation L (N : L) ≤ 1 := by
    simpa using P.valuation_le_one (K := L) (N : 𝓞 L)
  have he1 : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≤ 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_le_exp]
    norm_num
  set c := y * algebraMap L (P.adicCompletion L) ((N : L) * π) with hcdef
  have hc : c ≠ 0 := mul_ne_zero hy ((map_ne_zero _).2 (mul_ne_zero hN0 hπ0))
  obtain ⟨k₀, hk₀⟩ := adicCompletion_exists_approx_lt L P y c hc
  have hvc : Valued.v c = Valued.v y * (P.valuation L (N : L) * WithZero.exp (-1 : ℤ)) := by
    rw [hcdef, map_mul, valued_v_algebraMap_adicCompletion_foundation, map_mul, hπ]
  have hlt : Valued.v (y - algebraMap L _ k₀) < Valued.v y := by
    refine hk₀.trans_le ?_
    rw [hvc]
    exact mul_le_of_le_one_right' (mul_le_one' hN1 he1)
  have hyk : P.valuation L k₀ = Valued.v y := by
    rw [← valued_v_algebraMap_adicCompletion_foundation]
    apply Valuation.map_eq_of_sub_lt
    rwa [Valuation.map_sub_swap]
  have hk0 : k₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at hyk
    exact hy ((Valuation.zero_iff _).1 hyk.symm)
  refine ⟨Units.mk0 k₀ hk0, ?_, ?_, ?_⟩
  · rw [Units.val_mk0, hyk]
  · rw [Units.val_mk0, hyk]
    refine (hk₀.trans_eq hvc).le.trans ?_
    rw [mul_comm (Valued.v y)]
    gcongr ?_ * _
    exact mul_le_of_le_one_right' he1
  · rw [Units.val_mk0, hyk]
    refine (hk₀.trans_eq hvc).le.trans ?_
    rw [mul_comm (Valued.v y)]
    gcongr ?_ * _
    exact mul_le_of_le_one_left' hN1

/- English proof (translation)
Introduce `L _ _ N hN x`. Take `⟨hx0, hx1⟩` from `FiniteAdeleRing.isUnit_iff.1 x.isUnit`. Use `choose k hk using fun P => adicCompletion_exists_unit_approx L N hN P _ (hx0 P)`. Establish `hN0 : (N : 𝓞 L) ≠ 0` using `Nat.cast_ne_zero.2 hN.ne'`. Establish `h2 : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ Ideal.span {(N : 𝓞 L)}}.Finite` using `Ideal.finite_factors (by simpa using hN0)`.

Establish `hfin` using `(Filter.eventually_cofinite.1 hx1).union h2`. Use `⟨hfin.toFinset, k, fun P _ => hk P, fun P hP => ?_⟩` and prove the remaining obligations. Rewrite `hP` using `[Set.Finite.mem_toFinset, Set.mem_union, not_or]`. Take `⟨hP1, hP2⟩` from `hP`. Simplify using `only [Set.mem_ofPred_eq, not_not] at hP1 hP2`.

Conclude with `⟨hP1, fun hmem => hP2 (Ideal.dvd_span_singleton.2 hmem)⟩`.
-/
theorem finiteIdele_exists_local_approx :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), 0 < N → ∀ x : (FiniteAdeleRing (𝓞 L) L)ˣ, ∃ (S : Finset (HeightOneSpectrum (𝓞 L))) (k : HeightOneSpectrum (𝓞 L) → Lˣ), (∀ P ∈ S, Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ P.valuation L (N : L) * P.valuation L (k P : L) ∧ Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P - algebraMap L _ (k P : L)) ≤ WithZero.exp (-1 : ℤ) * P.valuation L (k P : L)) ∧ ∀ P, P ∉ S → Valued.v ((x : FiniteAdeleRing (𝓞 L) L) P) = 1 ∧ (N : 𝓞 L) ∉ P.asIdeal := by
  intro L _ _ N hN x
  obtain ⟨hx0, hx1⟩ := FiniteAdeleRing.isUnit_iff.1 x.isUnit
  choose k hk using fun P => adicCompletion_exists_unit_approx L N hN P _ (hx0 P)
  have hN0 : (N : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h2 : {P : HeightOneSpectrum (𝓞 L) | P.asIdeal ∣ Ideal.span {(N : 𝓞 L)}}.Finite :=
    Ideal.finite_factors (by simpa using hN0)
  have hfin := (Filter.eventually_cofinite.1 hx1).union h2
  refine ⟨hfin.toFinset, k, fun P _ => hk P, fun P hP => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_union, not_or] at hP
  obtain ⟨hP1, hP2⟩ := hP
  simp only [Set.mem_ofPred_eq, not_not] at hP1 hP2
  exact ⟨hP1, fun hmem => hP2 (Ideal.dvd_span_singleton.2 hmem)⟩

end GlobalTheory

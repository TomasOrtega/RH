import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayHomCompAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleProdOfEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldAtPrimeIsSepClosedOfFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DedekindPowerLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAwayQuotientEqLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNeighbourhoodKillsClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproximationQuotientsAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMaximalContaining
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ContrAtEqComapMap
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GlobalTheory.AffineCurveNbhd

noncomputable section

namespace GlobalTheory.CurveNbhdKill

def locKer {B : Type} [CommRing B] (f : B) (P : Ideal B) (hP : P.IsPrime) : Ideal B :=
  GlobalTheory.LocalSaturationContraction.satAt f P (hP := hP)

/- English proof (translation)
Take `⟨N, hN⟩` from `GlobalTheory.T.dedekind_power_localization B f hf P hP`. Take `⟨N', hN'⟩` from `GlobalTheory.T.dedekind_power_localization B f hf P' hP'`. Establish `hc : IsCoprime P P'` using `Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne hP hP' hne)`. Establish `hc' : IsCoprime (P ^ N) (P' ^ N')` using `hc.pow`. Rewrite `hc'`, the goal using `[Ideal.isCoprime_iff_sup_eq]`.

Conclude with `eq_top_iff.2 (hc' ▸ sup_le_sup (fun b hb => hN b hb) (fun b hb => hN' b hb))`.
-/
theorem locKer_coprime {B : Type} [CommRing B] [IsDedekindDomain B] (f : B) (hf : f ≠ 0) (P P' : Ideal B)
    (hP : P.IsMaximal) (hP' : P'.IsMaximal) (hne : P ≠ P') :
    IsCoprime (locKer f P hP.isPrime) (locKer f P' hP'.isPrime) := by
  obtain ⟨N, hN⟩ := GlobalTheory.T.dedekind_power_localization B f hf P hP
  obtain ⟨N', hN'⟩ := GlobalTheory.T.dedekind_power_localization B f hf P' hP'
  have hc : IsCoprime P P' := Ideal.isCoprime_iff_sup_eq.2 (Ideal.IsMaximal.coprime_of_ne hP hP' hne)
  have hc' : IsCoprime (P ^ N) (P' ^ N') := hc.pow
  rw [Ideal.isCoprime_iff_sup_eq] at hc' ⊢
  exact eq_top_iff.2 (hc' ▸ sup_le_sup (fun b hb => hN b hb) (fun b hb => hN' b hb))

/- English proof (translation)
Set `J : Ideal B` to `Submodule.comap (LinearMap.mulRight B b) (Ideal.span {f})`. Establish `hJ : J = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨M, hM, hJM⟩` from `Ideal.exists_le_maximal J hne`. Establish `hfJ : f ∈ J`.

Rewrite using `[Submodule.mem_comap, LinearMap.mulRight_apply]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)`. Take `⟨s, hs, hsb⟩` from `h M hM (hJM hfJ)`. Conclude with `hs (hJM (by rw [Submodule.mem_comap, LinearMap.mulRight_apply]; exact hsb))`. Establish `h1 : (1 : B) ∈ J` using `hJ ▸ Submodule.mem_top`.

Simplify `h1` using `[J]`.
-/
theorem mem_of_forall_locKer {B : Type} [CommRing B] (f b : B)
    (h : ∀ P : Ideal B, P.IsMaximal → f ∈ P → ∃ s : B, s ∉ P ∧ s * b ∈ Ideal.span {f}) :
    b ∈ Ideal.span {f} := by
  let J : Ideal B := Submodule.comap (LinearMap.mulRight B b) (Ideal.span {f})
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal J hne
    have hfJ : f ∈ J := by
      rw [Submodule.mem_comap, LinearMap.mulRight_apply]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self f)
    obtain ⟨s, hs, hsb⟩ := h M hM (hJM hfJ)
    exact hs (hJM (by rw [Submodule.mem_comap, LinearMap.mulRight_apply]; exact hsb))
  have h1 : (1 : B) ∈ J := hJ ▸ Submodule.mem_top
  simpa [J] using h1

/- English proof (translation)
Simplify using `[spMap, Spec.map_comp]`.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, Spec.map_comp]

variable (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B]
  [Algebra.FiniteType k B]

/- English proof (translation)
Establish `hqB : IsUnit (q : B)` using `by simpa using hq.map (algebraMap k B)`. Establish `hsep` using `GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType k B P`. Take `⟨D, _, _, _, Q, hQ, hQP, hres, hy⟩` from `GlobalTheory.T.etale_neighbourhood_kills_class q B hqB P hsep m i (by omega) y`. Take `⟨g, hS, hK⟩` from `GlobalTheory.T.away_quotient_span_eq_localization B D f hf P hP hfP Q hQ hQP hres`. Use `⟨Localization.Away g, inferInstance, inferInstance, inferInstance, hS, hK, ?_⟩` and prove the remaining obligations.

Rewrite using `[IsScalarTower.algebraMap_eq B D (Localization.Away g), spMap_comp', pull_comp, hy, map_zero]`.
-/
theorem onePoint (hq : IsUnit (q : k)) (f : B) (hf : f ≠ 0) (m i : ℤ) (hm : 1 ≤ m) (y : Ht q (sp B) m i)
    (P : Ideal B) (hP : P.IsMaximal) (hfP : f ∈ P) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧
      (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ locKer f P hP.isPrime) ∧
      pull _ (spMap (algebraMap B A)) _ _ y = 0 := by
  have hqB : IsUnit (q : B) := by simpa using hq.map (algebraMap k B)
  have hsep := GlobalTheory.T.residueField_atPrime_isSepClosed_of_finiteType k B P
  obtain ⟨D, _, _, _, Q, hQ, hQP, hres, hy⟩ := GlobalTheory.T.etale_neighbourhood_kills_class q B hqB P hsep m i (by omega) y
  obtain ⟨g, hS, hK⟩ := GlobalTheory.T.away_quotient_span_eq_localization B D f hf P hP hfP Q hQ hQP hres
  refine ⟨Localization.Away g, inferInstance, inferInstance, inferInstance, hS, hK, ?_⟩
  rw [IsScalarTower.algebraMap_eq B D (Localization.Away g), spMap_comp', pull_comp, hy, map_zero]

/- English proof (translation)
Introduce `q _ k B _ _ _ _ _ _ hq f hf hfu m i hm y`. Set `Pt` to `{P : Ideal B // P.IsMaximal ∧ f ∈ P}`. Use `haveI : Finite Pt := (GlobalTheory.T.finite_maximal_containing B f hf).to_subtype`. Use `letI : Fintype Pt := Fintype.ofFinite Pt`. Set `K : Pt → Ideal B` to `fun x => locKer f x.1 x.2.1.isPrime`.

Establish `key : ∀ T : Finset Pt, T.Nonempty → ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A), (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧ (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ ⨅ x ∈ T, K x) ∧ pull _ (spMap ( …`. Introduce `T hT`. Proceed by induction on `hT using Finset.Nonempty.cons_induction with`. Consider the case `singleton x`. Take `⟨A, _, _, _, hS, hK, hy⟩` from `onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2`.

Conclude with `⟨A, inferInstance, inferInstance, inferInstance, hS, fun b => by simpa [K] using hK b, hy⟩`. Consider the case `cons x T hx hT ih`. Take `⟨A₁, _, _, _, hS₁, hK₁, hy₁⟩` from `ih`. Take `⟨A₂, _, _, _, hS₂, hK₂, hy₂⟩` from `onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2`. Establish `hcop : IsCoprime (⨅ j ∈ T, K j) (K x)`.

Use `(Ideal.isCoprime_biInf fun j hj => ?_).symm` and prove the remaining obligations. Use `locKer_coprime f hf x.1 j.1 x.2.1 j.2.1 fun h => hx ?_` and prove the remaining obligations. Establish `: x = j` using `Subtype.ext h`. Conclude with `this ▸ hj`. Take `⟨hS, hK, hy⟩` from `GlobalTheory.T.approximation_quotients_agree q B A₁ A₂ f _ _ m i y hcop hS₁ hK₁ hS₂ hK₂ hy₁ hy₂`.

Use `⟨A₁ × A₂, inferInstance, inferInstance, GlobalTheory.T.etale_prod_of_etale B A₁ A₂ inferInstance inferInstance, hS, fun b => ?_, hy⟩` and prove the remaining obligations. Rewrite using `[hK b, Finset.cons_eq_insert, Finset.iInf_insert, inf_comm]`. Establish `hne : (Finset.univ : Finset Pt).Nonempty`. Establish `hspan : Ideal.span {f} ≠ ⊤` using `fun h => hfu (Ideal.span_singleton_eq_top.1 h)`. Take `⟨M, hM, hfM⟩` from `Ideal.exists_le_maximal _ hspan`.

Conclude with `⟨⟨M, hM, hfM (Ideal.mem_span_singleton_self f)⟩, Finset.mem_univ _⟩`. Take `⟨A, _, _, _, hS, hK, hy⟩` from `key Finset.univ hne`. Use `⟨A, inferInstance, inferInstance, inferInstance, ⟨hS, fun b hb => ?_⟩, hy⟩` and prove the remaining obligations. Establish `hb'` using `(hK b).1 hb`. Use `mem_of_forall_locKer f b fun P hP hfP => ?_` and prove the remaining obligations.

Use `(Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hb' ⟨P, hP, hfP⟩) (Finset.mem_univ _)` as an intermediate fact. Conclude with `this`.
-/
theorem exists_nbhd_pull_eq_zero : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ¬ IsUnit f → ∀ (m i : ℤ), 1 ≤ m → ∀ y : Ht q (sp B) m i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A') (_ : Algebra.Etale B A'), IsNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ y = 0 := by
  intro q _ k B _ _ _ _ _ _ hq f hf hfu m i hm y
  let Pt := {P : Ideal B // P.IsMaximal ∧ f ∈ P}
  haveI : Finite Pt := (GlobalTheory.T.finite_maximal_containing B f hf).to_subtype
  letI : Fintype Pt := Fintype.ofFinite Pt
  let K : Pt → Ideal B := fun x => locKer f x.1 x.2.1.isPrime
  have key : ∀ T : Finset Pt, T.Nonempty → ∃ (A : Type) (_ : CommRing A) (_ : Algebra B A) (_ : Algebra.Etale B A),
      (∀ a : A, ∃ b : B, a - algebraMap B A b ∈ Ideal.span {algebraMap B A f}) ∧
      (∀ b : B, algebraMap B A b ∈ Ideal.span {algebraMap B A f} ↔ b ∈ ⨅ x ∈ T, K x) ∧
      pull _ (spMap (algebraMap B A)) _ _ y = 0 := by
    intro T hT
    induction hT using Finset.Nonempty.cons_induction with
    | singleton x =>
      obtain ⟨A, _, _, _, hS, hK, hy⟩ := onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2
      exact ⟨A, inferInstance, inferInstance, inferInstance, hS, fun b => by simpa [K] using hK b, hy⟩
    | cons x T hx hT ih =>
      obtain ⟨A₁, _, _, _, hS₁, hK₁, hy₁⟩ := ih
      obtain ⟨A₂, _, _, _, hS₂, hK₂, hy₂⟩ := onePoint q k B hq f hf m i hm y x.1 x.2.1 x.2.2
      have hcop : IsCoprime (⨅ j ∈ T, K j) (K x) := by
        refine (Ideal.isCoprime_biInf fun j hj => ?_).symm
        refine locKer_coprime f hf x.1 j.1 x.2.1 j.2.1 fun h => hx ?_
        have : x = j := Subtype.ext h
        exact this ▸ hj
      obtain ⟨hS, hK, hy⟩ := GlobalTheory.T.approximation_quotients_agree q B A₁ A₂ f _ _ m i y hcop hS₁ hK₁ hS₂ hK₂ hy₁ hy₂
      refine ⟨A₁ × A₂, inferInstance, inferInstance, GlobalTheory.T.etale_prod_of_etale B A₁ A₂ inferInstance inferInstance, hS, fun b => ?_, hy⟩
      rw [hK b, Finset.cons_eq_insert, Finset.iInf_insert, inf_comm]
  have hne : (Finset.univ : Finset Pt).Nonempty := by
    have hspan : Ideal.span {f} ≠ ⊤ := fun h => hfu (Ideal.span_singleton_eq_top.1 h)
    obtain ⟨M, hM, hfM⟩ := Ideal.exists_le_maximal _ hspan
    exact ⟨⟨M, hM, hfM (Ideal.mem_span_singleton_self f)⟩, Finset.mem_univ _⟩
  obtain ⟨A, _, _, _, hS, hK, hy⟩ := key Finset.univ hne
  refine ⟨A, inferInstance, inferInstance, inferInstance, ⟨hS, fun b hb => ?_⟩, hy⟩
  have hb' := (hK b).1 hb
  refine mem_of_forall_locKer f b fun P hP hfP => ?_
  have := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hb' ⟨P, hP, hfP⟩) (Finset.mem_univ _)
  exact this

end GlobalTheory.CurveNbhdKill

end

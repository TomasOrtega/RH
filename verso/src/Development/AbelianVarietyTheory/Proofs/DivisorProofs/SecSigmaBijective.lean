import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Use `(Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => inferInstance⟩` and prove the remaining obligations. Take `⟨i, y, hy⟩` from `(sigmaOpenCover V).exists_eq x`. Conclude with `⟨i, y, hy⟩`.
-/
theorem ofArrows_sigmaι_mem_etale {ι : Type} (V : ι → Scheme.{0}) :
    Presieve.ofArrows V (Sigma.ι V) ∈ Scheme.etalePrecoverage (∐ V) := by
  refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x => ?_, fun i => inferInstance⟩
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover V).exists_eq x
  exact ⟨i, y, hy⟩

/- English proof (translation)
Establish `hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _)` using `(isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond`. Establish `hmem : (⊥ : Sieve Z) ∈ Scheme.etaleTopology Z` using `Scheme.bot_mem_grothendieckTopology (P := @Etale) Z`. Use `⟨fun a b => (hF _ hmem).isSeparatedFor.ext fun _ _ hf => ?_⟩` and prove the remaining obligations. Simplify using `at hf`.
-/
theorem sec_subsingleton_of_isEmpty {R : Type} [CommRing R] (F : Shv R) (Z : Scheme.{0}) [IsEmpty Z] :
    Subsingleton (Sec F Z) := by
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond
  have hmem : (⊥ : Sieve Z) ∈ Scheme.etaleTopology Z := Scheme.bot_mem_grothendieckTopology (P := @Etale) Z
  refine ⟨fun a b => (hF _ hmem).isSeparatedFor.ext fun _ _ hf => ?_⟩
  simp at hf

/- English proof (translation)
Introduce `R _ F ι V`. Establish `hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _)` using `(isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond`. Establish `h` using `hF.isSheafFor _ (Precoverage.generate_mem_toGrothendieck (ofArrows_sigmaι_mem_etale V))`. Rewrite `h` using `[Presieve.isSheafFor_arrows_iff]`. Establish `hc : ∀ x : ∀ i, Sec F (V i), Presieve.Arrows.Compatible (F.obj ⋙ forget _) (Sigma.ι V) x`.

Introduce `x i j Z gi gj hij`. Distinguish the cases in `e : i = j`. Substitute `e` using the available equality. Take `rfl` from `(cancel_mono (Sigma.ι V i)).1 hij`. Both sides reduce to the same expression.

Establish `: IsEmpty Z` using `⟨fun z => (isEmpty_pullback_sigmaι_of_ne V e).false ((pullback.lift gi gj hij).base z)⟩`. Use `sec_subsingleton_of_isEmpty F Z` as an intermediate fact. Conclude with `Subsingleton.elim _ _`. Use `⟨fun a b hab => ?_, fun x => ?_⟩` and prove the remaining obligations. Take `⟨t, -, ht⟩` from `h (fun i => Sec.res (Sigma.ι V i) a) (hc _)`.

Conclude with `(ht a fun i => rfl).trans (ht b fun i => (congrFun hab i).symm).symm`. Take `⟨t, ht, -⟩` from `h x (hc x)`. Conclude with `⟨t, funext ht⟩`.
-/
theorem sec_sigma_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) {ι : Type} (V : ι → Scheme.{0}), Function.Bijective fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a := by
  intro R _ F ι V
  have hF : Presieve.IsSheaf Scheme.etaleTopology (F.obj ⋙ forget _) :=
    (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose Scheme.etaleTopology (forget (ModuleCat.{1} (ULift.{1} R)))).obj F).cond
  have h := hF.isSheafFor _ (Precoverage.generate_mem_toGrothendieck (ofArrows_sigmaι_mem_etale V))
  rw [Presieve.isSheafFor_arrows_iff] at h
  have hc : ∀ x : ∀ i, Sec F (V i), Presieve.Arrows.Compatible (F.obj ⋙ forget _) (Sigma.ι V) x := by
    intro x i j Z gi gj hij
    by_cases e : i = j
    · subst e
      obtain rfl := (cancel_mono (Sigma.ι V i)).1 hij
      rfl
    · have : IsEmpty Z := ⟨fun z => (isEmpty_pullback_sigmaι_of_ne V e).false ((pullback.lift gi gj hij).base z)⟩
      have := sec_subsingleton_of_isEmpty F Z
      exact Subsingleton.elim _ _
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · obtain ⟨t, -, ht⟩ := h (fun i => Sec.res (Sigma.ι V i) a) (hc _)
    exact (ht a fun i => rfl).trans (ht b fun i => (congrFun hab i).symm).symm
  · obtain ⟨t, ht, -⟩ := h x (hc x)
    exact ⟨t, funext ht⟩

end GlobalTheory.EtC

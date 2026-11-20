import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsBasicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBijectiveOfTermwiseBijectStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackPushforwardFunctorialStatement

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.LevelCmp

variable {R : Type} [CommRing R]

/- English proof (translation)
The claim follows from `funext fun x => (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 a b I n x`.
-/
theorem cpull_comp_fun {K L M : Cx R} (a : K ⟶ L) (b : L ⟶ M) (I : Cx R) (n : ℤ) :
    ⇑(cpull (a ≫ b) I n) = ⇑(cpull a I n) ∘ ⇑(cpull b I n) :=
  funext fun x => (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 a b I n x

/- English proof (translation)
Take `⟨hid, -, -, -, hhom⟩` from `GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R`. Establish `h1` using `(hhom _ _ ⟨e.homotopyHomInvId⟩ I n).1`. Establish `h2` using `(hhom _ _ ⟨e.homotopyInvHomId⟩ I n).1`. Establish `l1 : ∀ y, cpull e.hom I n (cpull e.inv I n y) = y` using `fun y => by`. Rewrite using `[← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.hom e.inv I n y, h1]`.

Conclude with `(hid _ _ _ _).1`. Establish `l2 : ∀ x, cpull e.inv I n (cpull e.hom I n x) = x` using `fun x => by`. Rewrite using `[← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.inv e.hom I n x, h2]`. Conclude with `(hid _ _ _ _).1`. Conclude with `⟨Function.LeftInverse.injective l2, Function.RightInverse.surjective l1⟩`.
-/
theorem cpull_bij_of_heq {K L : Cx R} (e : HomotopyEquiv K L) (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull e.hom I n) := by
  obtain ⟨hid, -, -, -, hhom⟩ := GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R
  have h1 := (hhom _ _ ⟨e.homotopyHomInvId⟩ I n).1
  have h2 := (hhom _ _ ⟨e.homotopyInvHomId⟩ I n).1
  have l1 : ∀ y, cpull e.hom I n (cpull e.inv I n y) = y := fun y => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.hom e.inv I n y, h1]; exact (hid _ _ _ _).1
  have l2 : ∀ x, cpull e.inv I n (cpull e.hom I n x) = x := fun x => by
    rw [← (GlobalTheory.T.hypercohomologyPullbackPushforward_functorial R).2.1 e.inv e.hom I n x, h2]; exact (hid _ _ _ _).1
  exact ⟨Function.LeftInverse.injective l2, Function.RightInverse.surjective l1⟩

/- English proof (translation)
The claim follows from `cpull_bij_of_heq (HomotopyEquiv.ofIso (asIso f)) I n`.
-/
theorem cpull_bij_of_iso {K L : Cx R} (f : K ⟶ L) [IsIso f] (I : Cx R) (n : ℤ) :
    Function.Bijective (cpull f I n) :=
  cpull_bij_of_heq (HomotopyEquiv.ofIso (asIso f)) I n

end GlobalTheory.EtC.LevelCmp

open GlobalTheory.EtC.LevelCmp in

/- English proof (translation)
Introduce `R _ E E' f F hlev`. Take `⟨hle, hnat, -⟩` from `GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R`. Take `⟨e, -, he⟩` from `GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R`. Take `⟨-, hinj, hge, -⟩` from `GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F`. Use `haveI := hle E`.

Use `haveI := hle E'`. Use `haveI := hge`. Introduce `n`. Use `GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective R (res R F) hinj ((chains R).map f) ?_ n` and prove the remaining obligations. Introduce `p k`.

Break down `le_or_gt p 0 with hp | hp` into its components or cases. Take `⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ)` from `⟨(-p).toNat, by omega⟩ set φ := f.app (op (SimplexCategory.mk m))`. Establish `hfree : Function.Bijective (cpull ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map φ)) (res R F) k)`. Establish `hc` using `congrArg (fun g => ⇑(cpull g (res R F) k)) (he φ)`. Simplify using `only [cpull_comp_fun] at hc`.

Establish `hr : Function.Bijective (⇑(cpull (e _).hom (res R F) k) ∘ ⇑(cpull ((chains R).map (disc.map φ)) (res R F) k))` using `(cpull_bij_of_heq (e _) _ k).comp (hlev (op (SimplexCategory.mk m)) k)`. Rewrite `hr` using `[hc]`. Conclude with `(Function.Bijective.of_comp_iff _ (cpull_bij_of_heq (e _) _ k)).1 hr`. Establish `hg : ((chains R).map f).f (-(m : ℤ)) = (chainsXIso R E m).hom ≫ (free R).map φ ≫ (chainsXIso R E' m).inv`. Rewrite using `[← Category.assoc, ← hnat f m]`.

Simplify using the standard rewrite rules. Rewrite using `[hg, Functor.map_comp, Functor.map_comp, cpull_comp_fun, cpull_comp_fun]`. Conclude with `(cpull_bij_of_iso _ _ k).comp (hfree.comp (cpull_bij_of_iso _ _ k))`. Establish `h1 : IsZero (((chains R).obj E).X p)` using `CochainComplex.isZero_of_isStrictlyLE _ 0 p hp`. Establish `h2 : IsZero (((chains R).obj E').X p)` using `CochainComplex.isZero_of_isStrictlyLE _ 0 p hp`.

Use `haveI : IsIso (((chains R).map f).f p) := ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩`. Conclude with `cpull_bij_of_iso _ _ k`.
-/
theorem GlobalTheory.EtC.levelwise_eqv : GlobalTheory.EtC.A3 := by
  intro R _ E E' f F hlev
  obtain ⟨hle, hnat, -⟩ := GlobalTheory.T.chains_map_and_d_eq_sum_neg_one_pow_smul_delta R
  obtain ⟨e, -, he⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  obtain ⟨-, hinj, hge, -⟩ := GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F
  haveI := hle E; haveI := hle E'; haveI := hge
  intro n
  refine GlobalTheory.T.hypercohomologyPullback_bijective_of_termwise_bijective R (res R F) hinj ((chains R).map f) ?_ n
  intro p k
  rcases le_or_gt p 0 with hp | hp
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨(-p).toNat, by omega⟩
    set φ := f.app (op (SimplexCategory.mk m))

    have hfree : Function.Bijective
        (cpull ((CochainComplex.singleFunctor (Shv R) 0).map ((free R).map φ)) (res R F) k) := by
      have hc := congrArg (fun g => ⇑(cpull g (res R F) k)) (he φ)
      simp only [cpull_comp_fun] at hc
      have hr : Function.Bijective (⇑(cpull (e _).hom (res R F) k) ∘
          ⇑(cpull ((chains R).map (disc.map φ)) (res R F) k)) :=
        (cpull_bij_of_heq (e _) _ k).comp (hlev (op (SimplexCategory.mk m)) k)
      rw [hc] at hr
      exact (Function.Bijective.of_comp_iff _ (cpull_bij_of_heq (e _) _ k)).1 hr
    have hg : ((chains R).map f).f (-(m : ℤ)) =
        (chainsXIso R E m).hom ≫ (free R).map φ ≫ (chainsXIso R E' m).inv := by
      rw [← Category.assoc, ← hnat f m]; simp
    rw [hg, Functor.map_comp, Functor.map_comp, cpull_comp_fun, cpull_comp_fun]
    exact (cpull_bij_of_iso _ _ k).comp (hfree.comp (cpull_bij_of_iso _ _ k))
  · have h1 : IsZero (((chains R).obj E).X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    have h2 : IsZero (((chains R).obj E').X p) := CochainComplex.isZero_of_isStrictlyLE _ 0 p hp
    haveI : IsIso (((chains R).map f).f p) := ⟨⟨0, h1.eq_of_src _ _, h2.eq_of_src _ _⟩⟩
    exact cpull_bij_of_iso _ _ k

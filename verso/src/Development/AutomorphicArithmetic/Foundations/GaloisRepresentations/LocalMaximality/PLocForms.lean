import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ResidueOfTraceIsFiberSum
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.HsSum
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section LocFormsAux

private def Hs {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V]
    (B : Subalgebra ℂ L) (P : Finset ι) (g : ι → V) (w : V) : Prop :=
  ∃ c : ι → L, (∀ S, c S ∈ B) ∧ w = ∑ S ∈ P, c S • g S

variable {L V ι : Type} [Field L] [Algebra ℂ L] [AddCommGroup V] [Module L V]
  {B : Subalgebra ℂ L} {P : Finset ι} {g : ι → V}

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩`.
-/
private lemma Hs_zero : Hs B P g 0 := ⟨fun _ => 0, fun _ => B.zero_mem, by simp⟩

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Take `⟨c', hc', rfl⟩` from `h'`. Conclude with `⟨fun S => c S + c' S, fun S => B.add_mem (hc S) (hc' S), by`. Simplify using `[add_smul, Finset.sum_add_distrib]⟩`.
-/
private lemma Hs_add {w w' : V} (h : Hs B P g w) (h' : Hs B P g w') : Hs B P g (w + w') := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨c', hc', rfl⟩ := h'
  exact ⟨fun S => c S + c' S, fun S => B.add_mem (hc S) (hc' S), by
    simp [add_smul, Finset.sum_add_distrib]⟩

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Conclude with `⟨fun S => b * c S, fun S => B.mul_mem hb (hc S), by`. Simplify using `[Finset.smul_sum, mul_smul]⟩`.
-/
private lemma Hs_smul {b : L} (hb : b ∈ B) {w : V} (h : Hs B P g w) : Hs B P g (b • w) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun S => b * c S, fun S => B.mul_mem hb (hc S), by
    simp [Finset.smul_sum, mul_smul]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun T => if T = S then 1 else 0, fun T => by dsimp only; split_ifs <;> simp [B.one_mem, B.zero_mem], by simp [ite_smul, Finset.sum_ite_eq', hS]⟩`.
-/
private lemma Hs_single [DecidableEq ι] {S : ι} (hS : S ∈ P) : Hs B P g (g S) :=
  ⟨fun T => if T = S then 1 else 0, fun T => by dsimp only; split_ifs <;> simp [B.one_mem, B.zero_mem], by
    simp [ite_smul, Finset.sum_ite_eq', hS]⟩

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qh70.Hs_sum s f h`.
-/
private lemma Hs_sum {α : Type} (s : Finset α) (f : α → V) (h : ∀ a ∈ s, Hs B P g (f a)) :
    Hs B P g (∑ a ∈ s, f a) :=
  _root_.UpperTheory.Reformulated.B.Qh70.Hs_sum s f h

/- English proof (translation)
Use `set σ := Tuple.sort f`. Establish `hs : StrictMono (f ∘ σ)` using `(Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)`. Establish `hu : f ∘ σ = S.orderEmbOfFin rfl` using `Finset.orderEmbOfFin_unique rfl (fun a => hS _) hs`. Establish `hp` using `(ExteriorAlgebra.ιMulti L S.card (M := V)).map_perm (fun a => t (f a)) σ`. Establish `hv : ((fun a => t (f a)) ∘ σ) = fun a => t (S.orderEmbOfFin rfl a)`.

Use function extensionality and compare the values at `a`. Simplify using `using congrArg t (congrFun hu a)`. Rewrite `hp` using `[hv]`. Use `⟨((Equiv.Perm.sign σ : ℤˣ) : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[hp, Int.cast_smul_eq_zsmul, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]`.
-/
private lemma alt_sorted {V : Type} [AddCommGroup V] [Module L V] {d : ℕ} (t : Fin d → V)
    (S : Finset (Fin d)) (f : Fin S.card → Fin d) (hf : Function.Injective f)
    (hS : ∀ a, f a ∈ S) :
    ∃ n : ℤ, ExteriorAlgebra.ιMulti L S.card (fun a => t (f a)) =
      (n : L) • ExteriorAlgebra.ιMulti L S.card (fun a => t (S.orderEmbOfFin rfl a)) := by
  set σ := Tuple.sort f
  have hs : StrictMono (f ∘ σ) :=
    (Tuple.monotone_sort f).strictMono_of_injective (hf.comp σ.injective)
  have hu : f ∘ σ = S.orderEmbOfFin rfl :=
    Finset.orderEmbOfFin_unique rfl (fun a => hS _) hs
  have hp := (ExteriorAlgebra.ιMulti L S.card (M := V)).map_perm (fun a => t (f a)) σ
  have hv : ((fun a => t (f a)) ∘ σ) = fun a => t (S.orderEmbOfFin rfl a) := by
    funext a
    simpa using congrArg t (congrFun hu a)
  rw [hv] at hp
  refine ⟨((Equiv.Perm.sign σ : ℤˣ) : ℤ), ?_⟩
  rw [hp, Int.cast_smul_eq_zsmul, ← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]

/- English proof (translation)
Establish `h` using `(ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_sum (fun j l => c j l • t l)`. Simplify using `only [AlternatingMap.coe_multilinearMap] at h`. Rewrite using `[h]`. Use `Finset.sum_congr rfl fun f _ => ?_` and prove the remaining obligations. Conclude with `(ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_smul_univ _ _`.
-/
private lemma alt_expand {V : Type} [AddCommGroup V] [Module L V] {q d : ℕ} (t : Fin d → V)
    (c : Fin q → Fin d → L) :
    ExteriorAlgebra.ιMulti L q (fun j => ∑ l, c j l • t l) =
      ∑ f : Fin q → Fin d, (∏ j, c j (f j)) • ExteriorAlgebra.ιMulti L q (fun j => t (f j)) := by
  have h := (ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_sum
    (fun j l => c j l • t l)
  simp only [AlternatingMap.coe_multilinearMap] at h
  rw [h]
  refine Finset.sum_congr rfl fun f _ => ?_
  exact (ExteriorAlgebra.ιMulti L q (M := V)).toMultilinearMap.map_smul_univ _ _

end LocFormsAux

/- English proof (translation)
Introduce `hone F L _ _ _ _ _ _ d x hfc hr e q w`. Establish `ht : ∀ j, tt L x j ∈ loc (rB ℂ L (xv x) {0}) e.1` using `fun j => ⟨1, by simp, by simpa [tt] using tco_mem ℂ L (xv x) j⟩`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Express the relevant statement in the definitionally equal form `Hs _ _ _ w`.

Use `Submodule.span_induction ?_ Hs_zero (fun _ _ _ _ => Hs_add) ?_ hw` and prove the remaining obligations. Introduce and unpack `_ ⟨b, hb, v, hv, rfl⟩`. Use `Hs_smul hb ?_` and prove the remaining obligations. Use `choose c hcB hcD using fun j => hone F L d x hfc hr e (v j) (hv j)`. Simplify using `only [hcD]`.

Rewrite using `[alt_expand]`. Use `Hs_sum _ _ fun f _ => Hs_smul (Subalgebra.prod_mem _ fun j _ => hcB j _) ?_` and prove the remaining obligations. Distinguish the cases in `hf : Function.Injective f`. Take `⟨S, hS⟩ : ∃ S, S = Finset.univ.image f` from `⟨_, rfl⟩`. Establish `hcard : S.card = q`.

Rewrite using `[hS, Finset.card_image_of_injective _ hf]`. Simplify using the standard rewrite rules. Substitute `hcard` using the available equality. Take `⟨n, hn⟩` from `alt_sorted (L := L) (fun l => D ℂ L (tt L x l)) S f hf (fun a => by simp [hS])`. Rewrite using `[hn]`.

Conclude with `Hs_smul (intCast_mem _ n) (Hs_single (g := dtS L x) (by simp))`. Establish `: ¬ Function.Injective (fun j => D ℂ L (tt L x (f j)))` using `fun h => hf fun a b hab => h (by simp [hab])`. Rewrite using `[AlternatingMap.map_eq_zero_of_not_injective _ _ this]`. Conclude with `Hs_zero`. Introduce `a w _ h`.

Rewrite using `[← algebraMap_smul L a w]`. Conclude with `Hs_smul (Subalgebra.algebraMap_mem _ a) h`. Introduce and unpack `⟨c, hc, rfl⟩`. Use `Submodule.sum_mem _ fun S hS => ?_` and prove the remaining obligations. Establish `hcard` using `(Finset.mem_powersetCard.1 hS).2`.

Substitute `hcard` using the available equality. Conclude with `Submodule.subset_span ⟨c S, hc S, fun a => tt L x (S.orderEmbOfFin rfl a), fun j => ht _, rfl⟩`.
-/
theorem UpperTheory.Gal.productCup_of_system.locForms_of :
    LocOne → LocForms := by
  intro hone F L _ _ _ _ _ _ d x hfc hr e q w
  have ht : ∀ j, tt L x j ∈ loc (rB ℂ L (xv x) {0}) e.1 := fun j =>
    ⟨1, by simp, by simpa [tt] using tco_mem ℂ L (xv x) j⟩
  constructor
  · intro hw
    change Hs _ _ _ w
    refine Submodule.span_induction ?_ Hs_zero (fun _ _ _ _ => Hs_add) ?_ hw
    · rintro _ ⟨b, hb, v, hv, rfl⟩
      refine Hs_smul hb ?_
      choose c hcB hcD using fun j => hone F L d x hfc hr e (v j) (hv j)
      simp only [hcD]
      rw [alt_expand]
      refine Hs_sum _ _ fun f _ => Hs_smul (Subalgebra.prod_mem _ fun j _ => hcB j _) ?_
      by_cases hf : Function.Injective f
      · obtain ⟨S, hS⟩ : ∃ S, S = Finset.univ.image f := ⟨_, rfl⟩
        have hcard : S.card = q := by
          rw [hS, Finset.card_image_of_injective _ hf]; simp
        subst hcard
        obtain ⟨n, hn⟩ := alt_sorted (L := L) (fun l => D ℂ L (tt L x l)) S f hf
          (fun a => by simp [hS])
        rw [hn]
        exact Hs_smul (intCast_mem _ n) (Hs_single (g := dtS L x) (by simp))
      · have : ¬ Function.Injective (fun j => D ℂ L (tt L x (f j))) := fun h =>
          hf fun a b hab => h (by simp [hab])
        rw [AlternatingMap.map_eq_zero_of_not_injective _ _ this]
        exact Hs_zero
    · intro a w _ h
      rw [← algebraMap_smul L a w]
      exact Hs_smul (Subalgebra.algebraMap_mem _ a) h
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun S hS => ?_
    have hcard := (Finset.mem_powersetCard.1 hS).2
    subst hcard
    exact Submodule.subset_span ⟨c S, hc S, fun a => tt L x (S.orderEmbOfFin rfl a),
      fun j => ht _, rfl⟩

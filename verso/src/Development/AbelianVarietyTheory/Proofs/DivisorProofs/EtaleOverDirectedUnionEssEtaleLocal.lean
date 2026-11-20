import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalRingOfLocalizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAdjoinBaseChangeImageStatement
open IsLocalRing TensorProduct

namespace GlobalTheory.EtaleOverDirectedUnion

/- English proof (translation)
Introduce `R S' E _ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨ψ⟩⟩ P hP`. Use `letI : Algebra (Localization.AtPrime q) S' := ψ.toRingHom.toAlgebra`. Use `letI : Algebra (Localization.AtPrime q) E := ((algebraMap S' E).comp ψ.toRingHom).toAlgebra`. Use `haveI : IsScalarTower (Localization.AtPrime q) S' E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`. Use `haveI : Algebra.Etale (Localization.AtPrime q) S' := Algebra.Etale.of_equiv (R := Localization.AtPrime q) ({ ψ.toRingEquiv with commutes' := fun _ => rfl } : Localization.AtPrime q ≃ₐ[Localization.AtPrime q] S')`.

Use `haveI : Algebra.Etale (Localization.AtPrime q) E := Algebra.Etale.comp (Localization.AtPrime q) S' E`. Use `haveI : IsScalarTower R (Localization.AtPrime q) E := IsScalarTower.of_algebraMap_eq (fun r => by show algebraMap R E r = algebraMap S' E (ψ (algebraMap R _ r))`. Rewrite using `[ψ.commutes, ← IsScalarTower.algebraMap_apply])`. Conclude with `GlobalTheory.T.etale_local_ring_of_localization R A E q P`.
-/
theorem localRing_of_etale_over_essEtale : ∀ (R S' E : Type) [CommRing R] [CommRing S'] [CommRing E] [Algebra R S'] [Algebra S' E] [Algebra R E] [IsScalarTower R S' E] [Algebra.Etale S' E], (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] S')) → ∀ (P : Ideal E) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R S' E _ _ _ _ _ _ _ _ ⟨A, _, _, _, q, _, ⟨ψ⟩⟩ P hP
  letI : Algebra (Localization.AtPrime q) S' := ψ.toRingHom.toAlgebra
  letI : Algebra (Localization.AtPrime q) E := ((algebraMap S' E).comp ψ.toRingHom).toAlgebra
  haveI : IsScalarTower (Localization.AtPrime q) S' E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.Etale (Localization.AtPrime q) S' :=
    Algebra.Etale.of_equiv (R := Localization.AtPrime q)
      ({ ψ.toRingEquiv with commutes' := fun _ => rfl } : Localization.AtPrime q ≃ₐ[Localization.AtPrime q] S')
  haveI : Algebra.Etale (Localization.AtPrime q) E := Algebra.Etale.comp (Localization.AtPrime q) S' E
  haveI : IsScalarTower R (Localization.AtPrime q) E := IsScalarTower.of_algebraMap_eq (fun r => by
    show algebraMap R E r = algebraMap S' E (ψ (algebraMap R _ r))
    rw [ψ.commutes, ← IsScalarTower.algebraMap_apply])
  exact GlobalTheory.T.etale_local_ring_of_localization R A E q P

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `y _`. Rewrite using `[← e.symm_apply_apply y]`. Proceed by induction on `e y using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `tmul s b`. Establish `: s ⊗ₜ[A₀] b = s • ((1 : S) ⊗ₜ[A₀] b)` using `by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Rewrite using `[this, map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)`.

Consider the case `add x z hx hz => rw [map_add]`. Conclude with `add_mem hx hz`.
-/
theorem span_one_tmul_eq_top (S B : Type) [CommRing S] [CommRing B] [Algebra S B] (A₀ B₀ : Type)
    [CommRing A₀] [CommRing B₀] [Algebra A₀ S] [Algebra A₀ B₀] (e : B ≃ₐ[S] S ⊗[A₀] B₀) :
    Submodule.span S (Set.range (fun b : B₀ => e.symm (1 ⊗ₜ b))) = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [← e.symm_apply_apply y]
  induction e y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul s b =>
    have : s ⊗ₜ[A₀] b = s • ((1 : S) ⊗ₜ[A₀] b) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
  | add x z hx hz => rw [map_add]; exact add_mem hx hz

/- English proof (translation)
Take `⟨t, rfl⟩` from `h`. Use `choose f hf using hcov`. Take `⟨M, hM⟩` from `Finset.exists_le (t.image f)`. Conclude with `⟨M, Algebra.adjoin_le fun s hs => hmono (hM _ (Finset.mem_image_of_mem f hs)) (hf s)⟩`.
-/
theorem fg_le_member {R S : Type} [CommRing R] [CommRing S] [Algebra R S] {ι : Type} [Preorder ι]
    [IsDirected ι (· ≤ ·)] [Nonempty ι] (Si : ι → Subalgebra R S) (hmono : Monotone Si)
    (hcov : ∀ s : S, ∃ i, s ∈ Si i) (A₀ : Subalgebra R S) (h : A₀.FG) :
    ∃ i, A₀ ≤ Si i := by
  classical
  obtain ⟨t, rfl⟩ := h
  choose f hf using hcov
  obtain ⟨M, hM⟩ := Finset.exists_le (t.image f)
  exact ⟨M, Algebra.adjoin_le fun s hs => hmono (hM _ (Finset.mem_image_of_mem f hs)) (hf s)⟩

/- English proof (translation)
Introduce `R S B _ _ _ _ _ _ _ _ ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩`. Take `⟨A₀, B₀, _, _, hfg, hét, ⟨e⟩⟩` from `Algebra.Etale.exists_subalgebra_fg R S B`. Take `⟨i₀, hi₀⟩` from `fg_le_member Si hmono hcov A₀ hfg`. Set `g : B₀ → B` to `fun b => e.symm (1 ⊗ₜ b)`. Set `C : {j // i₀ ≤ j} → Subalgebra R B` to `fun j => Algebra.adjoin R ((algebraMap S B) '' (Si j.1 : Set S) ∪ Set.range g)`.

Establish `hdir : IsDirected {j // i₀ ≤ j} (· ≤ ·)` using `⟨fun a b => by`. Take `⟨k, hak, hbk⟩` from `directed_of (· ≤ ·) a.1 b.1`. Conclude with `⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩`. Establish `hCmono : Monotone C` using `fun a b hab => Algebra.adjoin_mono (Set.union_subset_union_left _ (Set.image_mono (hmono hab)))`. Use `⟨{j // i₀ ≤ j}, inferInstance, hdir, ⟨⟨i₀, le_rfl⟩⟩, C, hCmono, ?_, ?_⟩` and prove the remaining obligations.

Introduce `b`. Establish `hb : b ∈ Submodule.span S (Set.range g)`. Rewrite using `[span_one_tmul_eq_top S B A₀ B₀ e]`. Discharge the goal by the elementary cases of `trivial`. Proceed by induction on `hb using Submodule.span_induction with`.

Consider the case `mem x hx => exact ⟨⟨i₀, le_rfl⟩, Algebra.subset_adjoin (Or.inr hx)⟩`. Consider the case `zero => exact ⟨⟨i₀, le_rfl⟩, zero_mem _⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`.

Take `⟨k, hak, hbk⟩` from `directed_of (· ≤ ·) a b`. Conclude with `⟨k, add_mem (hCmono hak ha) (hCmono hbk hb)⟩`. Consider the case `smul s x _ hx`. Take `⟨a, ha⟩` from `hx`. Take `⟨j, hj⟩` from `hcov s`.

Take `⟨k, hak, hjk⟩` from `directed_of (· ≤ ·) a.1 j`. Use `⟨⟨k, a.2.trans hak⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.smul_def]`. Conclude with `mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, hmono hjk hj, rfl⟩)) (hCmono hak ha)`. Introduce `j P hP`.

Take `⟨_, _, _⟩` from `GlobalTheory.T.etale_adjoin_baseChange_image' R S B A₀ B₀ e (Si j.1) (hi₀.trans (hmono j.2))`. Conclude with `localRing_of_etale_over_essEtale R (Si j.1) (C j) (hloc j.1) P hP`.
-/
theorem construct : ∀ (R S B : Type) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B] [Algebra.Etale S B], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (C : ι → Subalgebra R B), Monotone C ∧ (∀ b : B, ∃ i, b ∈ C i) ∧ ∀ i (P : Ideal (C i)) (_ : P.IsPrime), (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime P)) := by
  intro R S B _ _ _ _ _ _ _ _ ⟨ι, _, _, _, Si, hmono, hcov, hloc⟩
  obtain ⟨A₀, B₀, _, _, hfg, hét, ⟨e⟩⟩ := Algebra.Etale.exists_subalgebra_fg R S B
  obtain ⟨i₀, hi₀⟩ := fg_le_member Si hmono hcov A₀ hfg
  let g : B₀ → B := fun b => e.symm (1 ⊗ₜ b)
  let C : {j // i₀ ≤ j} → Subalgebra R B := fun j =>
    Algebra.adjoin R ((algebraMap S B) '' (Si j.1 : Set S) ∪ Set.range g)
  have hdir : IsDirected {j // i₀ ≤ j} (· ≤ ·) := ⟨fun a b => by
    obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a.1 b.1
    exact ⟨⟨k, a.2.trans hak⟩, hak, hbk⟩⟩
  have hCmono : Monotone C := fun a b hab =>
    Algebra.adjoin_mono (Set.union_subset_union_left _ (Set.image_mono (hmono hab)))
  refine ⟨{j // i₀ ≤ j}, inferInstance, hdir, ⟨⟨i₀, le_rfl⟩⟩, C, hCmono, ?_, ?_⟩
  · intro b
    have hb : b ∈ Submodule.span S (Set.range g) := by
      rw [span_one_tmul_eq_top S B A₀ B₀ e]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx => exact ⟨⟨i₀, le_rfl⟩, Algebra.subset_adjoin (Or.inr hx)⟩
    | zero => exact ⟨⟨i₀, le_rfl⟩, zero_mem _⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      obtain ⟨k, hak, hbk⟩ := directed_of (· ≤ ·) a b
      exact ⟨k, add_mem (hCmono hak ha) (hCmono hbk hb)⟩
    | smul s x _ hx =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨j, hj⟩ := hcov s
      obtain ⟨k, hak, hjk⟩ := directed_of (· ≤ ·) a.1 j
      refine ⟨⟨k, a.2.trans hak⟩, ?_⟩
      rw [Algebra.smul_def]
      exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨s, hmono hjk hj, rfl⟩)) (hCmono hak ha)
  · intro j P hP
    obtain ⟨_, _, _⟩ := GlobalTheory.T.etale_adjoin_baseChange_image' R S B A₀ B₀ e (Si j.1) (hi₀.trans (hmono j.2))
    exact localRing_of_etale_over_essEtale R (Si j.1) (C j) (hloc j.1) P hP

end GlobalTheory.EtaleOverDirectedUnion
